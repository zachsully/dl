open Lazy

type ('a , 'b) mkNegPair  =  { getFst : 'a lazy_t option; getSnd : 'b lazy_t option;  }

let setfst mcd br =
  match mcd with
    None -> Some { getFst = Some br; getSnd = None; }
  | Some cd -> Some { getFst = Some br; getSnd = cd.getSnd; };;
let obsfst mcd =
  match mcd with
    None -> failwith "unmatched"
  | Some cd ->
     match cd.getFst with
       None -> failwith "unmatched"
     | Some br -> force br;;
let setsnd mcd br =
  match mcd with
    None -> Some { getFst = None; getSnd = Some br; }
  | Some cd -> Some { getFst = cd.getFst; getSnd = Some br; };;
let obssnd mcd =
  match mcd with
    None -> failwith "unmatched"
  | Some cd ->
     match cd.getSnd with
       None -> failwith "unmatched"
     | Some br -> force br;;

let prog = (obsfst (setfst (setsnd None (lazy 0)) (lazy 42)));;

print_int prog;;
print_newline ();;
