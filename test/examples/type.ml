type h = |A 
         |B 

type any = |Int of int
           |Str of string

type 'a lists = |Nil 
                |Cons of 'a * 'a list        


let id2 y =  y
 (*@  req y:#t' ; ens res : # t' @*)

let plus x y = x + y 
(*@  req x:#int /\ y:#int ; ens res : # int @*)

let deref x = !x 
(*@  req x:#Ref[t']  ; ens res : # t' @*)

let tail x = 
  (*@  req x:#Cons[t',Lists[t']]  ; ens res : # Lists[t'] $  req x:#Nil[]  ; ens res : # Err[] @*)
             match x with
             | Cons (x,xs) -> xs 
             | Nil -> failwith "not supported"        




let id3 x = id2 x 
 (*@  req x:#str ; ens res : # str @*)

let id4 y = 
(*@ req y:#Int[int] ; ens res:#Int[int] $ req y:#Str[str] ; ens res:#Str[str] $ req y:#__ ; ens res:#top@*)
        match y with 
        |Int x->Int (x+1) 
        |Str x -> Str ("not supported")
  

 let id y = let x = y in x;;
  (*@  forall t. req y:#t';   ens res: # t'  $ req y:#str ; ens res:#str $ req y->#int; ens  y->#int /\res=y $ req y -> # List[(int \/ str)]; ens res = y /\ y -> # List[(int \/ str)] @*)

(* let string_of_int x = failwith "to be implemented" *)
 (*@ req true; ens res : # Ref[y] @*)
(* let inc_inplace x = x := string_of_int !x +1 *)
 (*@ req true; ens res : # Ref[y] @*)
 
 (* let f t = 
    !t := 5
let test q= 
  let x = ref 2 in 
  let y = ref x in 
  f y;
  x := 3; print_int (!(!y)) ; q *)

