
open Parsing
open Hipcore
open Hiptypes

let type_predicates : (string, term list * state) Hashtbl.t = Hashtbl.create 32

let set_type_predicates (preds : type_pred list) =
  Hashtbl.reset type_predicates;
  List.iter (fun (name, args, st) -> Hashtbl.replace type_predicates name (args, st)) preds

let mk_pi_conj (ps : pi list) : pi =
  match ps with
  | [] -> True
  | hd :: tl -> List.fold_left (fun acc p -> And (acc, p)) hd tl

let sep_conj_opt (k1 : kappa) (k2 : kappa) : kappa =
  match k1, k2 with
  | EmptyHeap, k | k, EmptyHeap -> k
  | _ -> SepConj (k1, k2)

let rec subst_term (env : (string * term) list) (t : term) : term =
  match t with
  | Var v -> Option.value (List.assoc_opt v env) ~default:t
  | Const _ -> t
  | Rel (op, t1, t2) -> Rel (op, subst_term env t1, subst_term env t2)
  | BinOp (op, t1, t2) -> BinOp (op, subst_term env t1, subst_term env t2)
  | TNot t1 -> TNot (subst_term env t1)
  | TApp (f, args) -> TApp (f, List.map (subst_term env) args)
  | Construct (c, args) -> Construct (c, List.map (subst_term env) args)
  | TLambda _ -> t
  | TTuple ts -> TTuple (List.map (subst_term env) ts)
  | Type _ -> t

let rec subst_pi env p =
  match p with
  | True | False -> p
  | Atomic (op, t1, t2) -> Atomic (op, subst_term env t1, subst_term env t2)
  | And (p1, p2) -> And (subst_pi env p1, subst_pi env p2)
  | Or (p1, p2) -> Or (subst_pi env p1, subst_pi env p2)
  | Imply (p1, p2) -> Imply (subst_pi env p1, subst_pi env p2)
  | Not p1 -> Not (subst_pi env p1)
  | Predicate (name, args) -> Predicate (name, List.map (subst_term env) args)
  | Subsumption (t1, t2) -> Subsumption (subst_term env t1, subst_term env t2)
  | Colon (v, t) -> Colon (v, subst_term env t)

let rec subst_kappa env k =
  match k with
  | EmptyHeap -> k
  | PointsTo (v, t) -> PointsTo (v, subst_term env t)
  | SepConj (k1, k2) -> SepConj (subst_kappa env k1, subst_kappa env k2)

let subst_state env (p, k) = (subst_pi env p, subst_kappa env k)

let rec flatten_and (p : pi) : pi list =
  match p with
  | And (p1, p2) -> flatten_and p1 @ flatten_and p2
  | True -> []
  | _ -> [p]

let build_pred_env (formals : term list) (actuals : term list) =
  let rec aux fs as_ env =
    match fs, as_ with
    | [], [] -> Some (List.rev env)
    | Var x :: fs, a :: as_ -> aux fs as_ ((x, a) :: env)
    | _ -> None
  in
  aux formals actuals []

let expand_state_predicates_once ((p, k) : state) : state * bool =
  let predicates = flatten_and p in
  let expanded_ps, expanded_k, changed =
    List.fold_left
      (fun (acc_p, acc_k, changed) atom ->
        match atom with
        | Predicate (name, actuals) -> begin
            match Hashtbl.find_opt type_predicates name with
            | None -> (atom :: acc_p, acc_k, changed)
            | Some (formals, pred_state) -> begin
                match build_pred_env formals actuals with
                | None -> failwith (Printf.sprintf "invalid predicate arguments for %s" name)
                | Some env ->
                    let p', k' = subst_state env pred_state in
                    let acc_p = if p' = True then acc_p else p' :: acc_p in
                    let acc_k = sep_conj_opt acc_k k' in
                    (acc_p, acc_k, true)
              end
          end
        | _ -> (atom :: acc_p, acc_k, changed))
      ([], k, false)
      predicates
  in
  (mk_pi_conj (List.rev expanded_ps), expanded_k), changed

let expand_state_predicates (st : state) : state =
  let rec loop fuel state =
    if fuel <= 0 then state
    else
      let state', changed = expand_state_predicates_once state in
      if changed then loop (fuel - 1) state' else state'
  in
  loop 16 st

let rec expand_staged_spec_predicates (s : staged_spec) : staged_spec =
  match s with
  | Exists (v, s1) -> Exists (v, expand_staged_spec_predicates s1)
  | ForAll (v, s1) -> ForAll (v, expand_staged_spec_predicates s1)
    | Require (p, k) ->
      let p, k = expand_state_predicates (p, k) in
      Require (p, k)
    | NormalReturn (p, k) ->
      let p, k = expand_state_predicates (p, k) in
      NormalReturn (p, k)
  | HigherOrder _ -> s
  | Shift (b, k, body, x, cont) ->
      Shift (b, k, expand_staged_spec_predicates body, x, expand_staged_spec_predicates cont)
  | Reset s1 -> Reset (expand_staged_spec_predicates s1)
  | Sequence (s1, s2) -> Sequence (expand_staged_spec_predicates s1, expand_staged_spec_predicates s2)
  | Bind (v, s1, s2) -> Bind (v, expand_staged_spec_predicates s1, expand_staged_spec_predicates s2)
  | Disjunction (s1, s2) -> Disjunction (expand_staged_spec_predicates s1, expand_staged_spec_predicates s2)
  | RaisingEff (p, k, ins, t) ->
      let p, k = expand_state_predicates (p, k) in
      RaisingEff (p, k, ins, t)
  | TryCatch (p, k, (src, ((norm_p, norm_spec), ops)), ret) ->
      let p, k = expand_state_predicates (p, k) in
      let src = expand_staged_spec_predicates src in
      let norm_spec = expand_staged_spec_predicates norm_spec in
      let ops = List.map (fun (name, arg, spec) -> (name, arg, expand_staged_spec_predicates spec)) ops in
      TryCatch (p, k, (src, ((norm_p, norm_spec), ops)), ret)
  | Multi (s1, s2) -> Multi (expand_staged_spec_predicates s1, expand_staged_spec_predicates s2)
  | Assume s1 -> Assume (expand_staged_spec_predicates s1)

let handle_error parser lexbuf =
  try parser Lexer.token lexbuf with
    | Lexer.Lexing_error msg ->
      Printf.eprintf "Lexing error: %s\n" msg;
      failwith "lexer error"
    | Parser.Error ->
      let pos = Lexing.lexeme_start_p lexbuf in
      let line = pos.Lexing.pos_lnum in
      let column = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 in
      let token = Lexing.lexeme lexbuf in
      Printf.eprintf
        "Parse error at line %d, column %d: unexpected token '%s'\n" line column
        token;
      failwith "parse error"

let parse_staged_spec spec =
  handle_error Parser.parse_staged_spec (Lexing.from_string spec)
  |> expand_staged_spec_predicates

let parse_pi spec =
  handle_error Parser.parse_pi (Lexing.from_string spec)

let parse_lemma spec =
  let lemma = handle_error Parser.parse_lemma (Lexing.from_string spec) in
  { lemma with
    l_left = expand_staged_spec_predicates lemma.l_left;
    l_right = expand_staged_spec_predicates lemma.l_right }

let parse_kappa spec = Parser.parse_kappa Lexer.token (Lexing.from_string spec)

let parse_term spec = Parser.parse_term Lexer.token (Lexing.from_string spec)

let parse_state spec = Parser.parse_state Lexer.token (Lexing.from_string spec)

let parse_type_pred_decl spec =
  handle_error Parser.parse_type_pred_decl (Lexing.from_string spec)

let string_of_payload (p : Parsetree.payload) =
  match p with
  | PStr [{
      pstr_desc = Pstr_eval ({
        pexp_desc = Pexp_constant {
          pconst_desc = Pconst_string (annotation, _, _); _}; _}, _); _}] -> 
            Some annotation
  | _ -> None

let attribute_parser (attr_name : string) (payload_parser : Parsetree.payload -> 'a option) attr =
  let open Ocaml_compiler.Ocaml_common.Parsetree in
  (* TODO use ppxlib to do this matching instead; it would be a lot cleaner... *)
  if String.equal attr.attr_name.txt attr_name
  then payload_parser attr.attr_payload
  else None

let parse_spec_attribute = attribute_parser "spec" (fun p -> Option.map parse_staged_spec (string_of_payload p))
let parse_ignore_attribute = attribute_parser "ignore" (fun _ -> Some ())
let parse_lemma_attribute = attribute_parser "lemma" (fun p -> Option.map parse_lemma (string_of_payload p))

let extract_attribute parser attrs =
  match List.filter_map parser attrs with
  | item :: _ -> Some item
  | _ -> None

let extract_spec_attribute attrs = extract_attribute parse_spec_attribute attrs
let extract_ignore_attribute attrs = extract_attribute parse_ignore_attribute attrs
