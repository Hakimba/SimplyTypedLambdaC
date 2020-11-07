open Types


let cnt_terme = ref 0;;
module RefVar = Map.Make (String);;

let fresh_tvar () =
  incr cnt_terme;
  "t"^(string_of_int !cnt_terme)
;;

let barendregt (t:term) =
  let rec barend_rec t map = 
    match t with

    | TmVar(v) -> let _ = Printf.printf "TmVar = %s\n" v in
                  let res = try
                    TmVar((RefVar.find v map))
                  with
                    Not_found -> TmVar(v)
                  in res

    | TmAbs(name, term) ->  let _ = Printf.printf "TmAbs name = %s\n" name in
                            let new_v = fresh_tvar() in
                            let new_m = RefVar.add name new_v map in
                            TmAbs(new_v, barend_rec term new_m)

    | TmApp(t1, t2) -> TmApp(barend_rec t1 map, barend_rec t2 map)

    | TmList(seq) ->  let rec seqBarend l res = 
                        match l with
                          Nil -> res
                          | Cons(hd, tl) -> 
                              seqBarend tl (Cons((barend_rec hd map), res))
                      in TmList(seqBarend seq Nil)
    | _ -> t
  in
  barend_rec t RefVar.empty;;

let simple_eval = TmApp(TmAbs("x",TmAbs("y",TmVar("y"))), TmAbs("z",TmAbs("y",TmVar("z"))));;
(*Printf.printf "%s\n" (pretty_printer_term simple_eval);;
Printf.printf "%s\n" (pretty_printer_term (barendregt simple_eval));;*)
