type h = |A 
         |B 

type any = |Int of int
           |Str of string

type 'a list = |Nil 
                |Cons of 'a * 'a list       


let id2 y =  y
 (*@  req y:#t' ; ens res : # t'  @*)

let plus x y = x + y 
(*@  req x:#int /\ y:#int ; ens res : # int @*)

let apply f x = f x 
(*@  req f:#(a'-> b')  /\ x:#a' ; ens res : # b' @*)

let deref x = !x 
(*@  req x:#Ref[t']  ; ens res : # t' $ req x->#Ref[t']  ; ens  x->#Ref[t'] /\ res : # t' @*)

let tail x = 
  (*@  req x:#Cons[t',List[t']]  ; ens res : # List[t'] $  req x:#Nil[]  ; ens res : # Err[] 
        $ req x->#Cons[t',List[t']]  ; ens res : # List[t']
        $ req x->#Nil  ; ens res : # Err
        @*)
             match x with
             | Cons (x,xs) -> xs 
             | Nil -> failwith "not supported"        




let id3 x = id2 x 
 (*@  req x:#str ; ens res : # str @*)

let inc_if_int y = 
(*@ req y:#Int[int] ; ens res:#Int[int] $ req y:#Str[str] ; ens res:#Str[str] $ req y:#__ ; ens res:#top@*)
        match y with 
        |Int x->Int (x+1) 
        |Str x -> Str ("not supported")
  

 let id y = let x = y in x;;
  (*@  forall t. req y:#t';   ens res: # t'  $ req y:#str ; ens res:#str $ req y->#int; ens  y->#int /\res=y $ req y -> # List[(int \/ str)]; ens res = y /\ y -> # List[(int \/ str)] @*)

let string_of_ints x = failwith "assume" 
 (*@ assume req x:#int; ens res : #str @*)
let inc_inplace x = x := string_of_ints (!x +1)
 (*@ req x->#Ref[int]; ens x -> # Ref[str] @*)

let make_ref x = ref x
  (*@ req x:#a'; ens res -> # Ref[x] /\  x:#a' @*)




let update m v = m := v
(*@  req m->#Ref[t'] /\ v:#a' ; ens  m->#Ref[a']  @*)

let swap2 x  y  = 
(*@  req x->#Ref[a'] * y-> #Ref[b'] ; ens x->#Ref[b'] * y->#Ref[a']   @*)
              let v1 = !x in let v2 = !y in
            
              update x  v2  ;
              update y  v1 

let alise2 x y = swap2 x y 
(*@  req x->#Ref[a'] * y-> #Ref[b'] ; ens y->#Ref[a'] * x-> #Ref[b']   @*)



let swap x  y  = 
(*@  req x->#Ref[a'] /\ x=y ; ens x->#Ref[a'] /\ x=y $  
     req x->#Ref[a'] * y-> #Ref[b'] ; ens x->#Ref[b'] * y->#Ref[a']  @*)
              let v1 = !x in let v2 = !y in
            
              update x  v2  ;
              update y  v1 

let alise x y = swap x y 
(*@  req x->#Ref[a'] /\ x=y ; ens x->#Ref[a'] /\ x=y  $ 
     req x->#Ref[a'] * y-> #Ref[b'] ; ens y->#Ref[a'] * x-> #Ref[b'] @*)

let list_seg x = x
(*@  req x->#Cons[int, y] * y -> #Cons[int,z] * z->#Cons[int,Nil] ; ens x->#Cons[int, Cons[int, Cons[int,Nil]]] /\ res=x
$ req x->#Nil; ens x->#List[a'] /\ res = x
$ req x->#Cons[int, y] * y -> #Cons[int,z] * z->#Cons[int,Nil] ; ens x->#List[int] /\ res=x
$ req x->#Cons[1, y] * y -> #Cons[2,z] * z->#Cons[3,Nil] ; ens x->#List[int] /\ res=x
$ req x->#Cons[a', y] * y -> #List[a']; ens x->#List[a'] /\ res=x
$ req x->#Nil ; ens x->#Nil /\ res=x
@*)

let list_entail y =list_seg y 
(*@  req y->#List[a'] ; ens y->#List[a'] /\ res=y @*)

let two_pointer x  y  z= 
(*@  req x->#Ref[a'] * y->#Ref[b'] ; ens x->#Ref[Ref[b']]  
$  req x->#Ref[a'] /\ x=y ; ens x->#Ref[y] /\ x=y  @*)
               x := y

let check_spec_completeness x = tail x 
(*@ req x:#List[a']  ; ens res : # (List[a'] \/ Err[])@*)


let rec map f xs  = match xs with 
              (*@ req f:#Any /\ xs : #Nil ; ens  res : #Nil 
                 $ req f:# (a'-> b')  /\ xs :#Cons[a', List[a']]; ens res :#Cons[b', List[b']] 
                 $ req f:#Any /\ xs -> #Nil ; ens xs -> #Nil /\ res : #Nil 
                 $ req f:# (a'-> b')  /\ xs -> #Cons[a', List[a']]; ens  xs -> #Cons[a', List[a']] /\ res :#Cons[b', List[b']] 
                 @*)
              |Nil -> Nil 
              |Cons (y , ys) -> Cons ( f  y  , map f ys )



let more_args f x y = f x y 
(*@  req f:#(a'-> b'-> c') /\ x:#a' /\ y:#b' ; ens res : # c' @*)

let test x y = more_args plus x y 
(*@  req plus:#(int-> int-> int) /\ x:#int /\ y:#int ; ens res : # int @*)

let partial_app x = more_args plus x 
(*@  req plus:#(int-> int-> int) /\ x:#int ; ens res : # int -> int @*)

let partial_app2 y = 
(*@ req y:#int ; ens res : #int -> int @*)
partial_app y

let partial_app3 y = 
(*@ req y:#int ; ens res : #int -> int @*)
  test y

let maplist_int_string l f= 
   (*@ req l:#List[int] /\ f : # int->str; ens  res : #List[str] 
   $ req l->#List[int] /\ f : # int->str; ens   l->#List[int] /\ res : #List[str] 
   @*)
                        map f l 




(* let f t = 
    !t := 5
let test q= 
  let x = ref 2 in 
  let y = ref x in 
  f y;
  x := 3; print_int (!(!y)) ; q *)

