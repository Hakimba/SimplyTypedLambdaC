

let cnt_terme = ref 0;;
let max_eval = ref 1000;;
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

    | TmApp(t1, t2) -> let barendt1 = barend_rec t1 map in
                        let barendt2 = barend_rec t2 map in 
                      TmApp(barendt1, barendt2)

    (*| TmList(seq) ->  let rec seqBarend l res = 
                        match l with
                          Nil -> res
                          | Cons(hd, tl) -> 
                              seqBarend tl (Cons((barend_rec hd map), res))
                      in TmList(seqBarend seq Nil)*)
    | _ -> t
  in
  barend_rec t RefVar.empty;;

let substitute v ts t =
  let rec sub_rec t' = match t' with
      (TyVar x) -> if x = v then ts else t'
    | TyFun(t1,t2) -> let rt1 = sub_rec t1 in
                      let rt2 = sub_rec t2 in
                      TyFun(rt1,rt2)
    | TyInt -> t'
    | TyList(res) -> let sub = sub_rec res in TyList(sub)
    | TyForall(arg,res) -> let sub = sub_rec res in
                            TyForall(arg,sub)
  in sub_rec t
;;

(*Substitue x par a dans l*)
let instantie l x a = 
  let rec inst_rec l' = match l' with
    TmVar(v) as tv -> if v = x then a else tv

    | TmAbs(name, term) -> TmAbs(name,(inst_rec term))

    | TmApp(t1, t2) -> TmApp((inst_rec t1), (inst_rec t2))
      in inst_rec l
;;


let rec ltrcbv_etape term = let status = "KO" in
  match term with
    TmApp(TmAbs(name,body),t2) -> let inst = instantie body name t2 in
                                    ("OK",inst)
    | TmApp(t1, t2) -> let (status,resfun) = ltrcbv_etape t1 in
                        if status = "OK" then ("OK",TmApp(resfun,t2))
                        else
                          let (status,resarg) = ltrcbv_etape t2 in
                          if status = "OK" then ("OK",TmApp(t1,resarg))
                          else ltrcbv_etape t1



    | _ -> (status,term)

let ltrcbv t =
  let courant = ref (barendregt t) in
  let c = ref 0 in
  let _ = print_string (pretty_printer_term (!courant)) in
  try
    while (!c) < (!max_eval) do
      let (status,new_red) = ltrcbv_etape (!courant) in
      if status = "KO" then raise BreakLoop
      else
        print_string ("\n -> "^(pretty_printer_term new_red));
      courant := new_red;
      incr c
    done;
    if (!c) = (!max_eval) then print_string "\nSTOP trop de reductions" else ()
  with
    BreakLoop -> print_string "\névaluation terminée"

