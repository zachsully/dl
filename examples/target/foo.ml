open Lazy

type ('a , 'b) mkNegPair  =  { getFst : 'a lazy_t option; getSnd : 'b lazy_t option;  }

exception Unmatched
let bot = lazy (raise Unmatched);;

let setfst cd br =
  try let cdn = { getFst = Some br; getSnd = (force cd).getSnd; }
      in lazy cdn with
    Unmatched -> lazy { getFst = Some br; getSnd = None; }
let obsfst cd =
  match (force cd).getFst with
    None -> force bot
  | Some br -> force br;;
let setsnd cd br =
  try let cdn = { getFst = (force cd).getFst; getSnd = Some br; }
      in lazy cdn with
    Unmatched -> lazy { getFst = None; getSnd = Some br; }
let obssnd cd =
  match (force cd).getSnd with
    None -> force bot
  | Some br -> force br;;

let prog = (obsfst (setsnd (setfst bot (lazy 42)) (lazy 0)));;

print_int prog;;
print_newline ();;
