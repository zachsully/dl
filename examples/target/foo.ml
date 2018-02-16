open Lazy

type ('a , 'b) mkNegPair  =  { getFst : 'a; getSnd : 'b;  }

let prog = let setFst = (fun d -> (fun x -> lazy { getFst = x; getSnd = (force d).getSnd; })) in
           let setSnd = (fun d -> (fun x -> lazy { getFst = (force d).getFst; getSnd = x; })) in
           (force ((setFst ((setSnd (lazy (failwith "k"))) 0)) 42)).getFst;;

print_int prog;;
print_newline ();;
