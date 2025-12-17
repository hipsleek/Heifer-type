
type any = |Int of int
           |Str of string

type 'a lists = |Nil 
                |Cons of 'a * 'a lists        


let id2 y =  y
 (*@  req y:#int ; ens res : # t'  @*)

let update m v = m := v
(*@  req m->#Ref[t'] /\ v:#a' ; ens  m->#Ref[a']  @*)
let swap x  y  = 
(*@  req x->#Ref[a'] /\ x=y ; ens x->#Ref[a'] * y->#Ref[a'] $ req x->#Ref[a'] * y->#Ref[a'] ; ens x->#Ref[a'] /\ x=y @*)
              let v1 = !x in let v2 = !y in
            
              update x  v2  ;
              update y  v1 
let update m v = m := v
(*@  req m->#Ref[t'] /\ v:#a' ; ens  m->#Ref[a']  @*)

let list_seg x = x
(*@  req x->#Cons[int, y] * y -> #Cons[int,z] * z->#Cons[int,Nil] ; ens x->#Cons[int, Cons[int, Cons[int,Nil]]] /\ res=x
$ req x->#Nil; ens x->#List[a'] /\ res = x
$ req x->#Cons[int, y] * y -> #Cons[int,z] * z->#Cons[int,Nil] ; ens x->#List[int] /\ res=x
$ req x->#Cons[1, y] * y -> #Cons[2,z] * z->#Cons[3,Nil] ; ens x->#List[int] /\ res=x
@*)

let list_seg_fail y =list_seg y 
(*@  req y->#List[a'] ; ens y->#List[a'] /\ res=y @*)