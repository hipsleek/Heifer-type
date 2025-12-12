type h = |A 
         |B 

type any = |Int of int
           |Str of string

type 'a lists = |Nil 
                |Cons of 'a * 'a lists        


let id2 y =  y
 (*@  req y:#t' ; ens res : # t' @*)

let plus x y = x + y 
(*@  req x:#int /\ y:#int ; ens res : # int @*)

let apply f x = f x 
(*@  req f:#a'-> b' /\ x:#a' ; ens res : # b' @*)

let deref x = !x 
(*@  req x:#Ref[t']  ; ens res : # t' @*)

let tail x = 
  (*@  req x:#Cons[t',Lists[t']]  ; ens res : # Lists[t'] $  req x:#Nil[]  ; ens res : # Err[] @*)
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

let deref2 x = !x 
(*@  req x->#Ref[t']  ; ens  x->#Ref[t'] /\ res : # t' @*)

let update m v = m := v
(*@  req m->#Ref[t'] /\ v:#a' ; ens  m->#Ref[a']  @*)

let swap x  y  = 
(*@  req x->#Ref[a'] * y->#Ref[b'] ; ens x->#Ref[b'] * y->#Ref[a']   @*)
              let v1 = !x in let v2 = !y in
            
              update x  v2  ;
              update y  v1 

let rec map f xs = 
  (*@  req xs:#Nil ; ens res:#Nil   @*)
              match xs with 
              | Nil -> Nil 
              | Cons (y, ys) -> Cons(y, map f ys)


(* let f t = 
    !t := 5
let test q= 
  let x = ref 2 in 
  let y = ref x in 
  f y;
  x := 3; print_int (!(!y)) ; q *)

