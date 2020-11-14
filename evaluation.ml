
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

    | TmVar(v) -> let res = try
                    TmVar((RefVar.find v map))
                  with
                    Not_found -> TmVar(v)
                  in res

    | TmAbs(name, term) ->  let new_v = fresh_tvar() in
                            let new_m = RefVar.add name new_v map in
                            TmAbs(new_v, barend_rec term new_m)

    | TmApp(t1, t2) ->  let barendt1 = barend_rec t1 map in
                        let barendt2 = barend_rec t2 map in 
                        TmApp(barendt1, barendt2)

    | TmSeq(seq) ->  let rec seqBarend l res = 
                        match l with
                          [] -> res
                          | hd::tl -> 
                              seqBarend tl (res@[(barend_rec hd map)])
                      in TmSeq(seqBarend seq [])

    | TmLet(name, t1, t2) ->  let new_v = fresh_tvar() in
                              let eval_t1 = barend_rec t1 map in
                              let map2 = RefVar.add name new_v map in
                              let eval_t2 = barend_rec t2 map2 in
                              TmLet(new_v, eval_t1, eval_t2)

    | TmIfBz(cond, th, el) -> let bar_cond = barend_rec cond map in
                              let bar_th = barend_rec th map in
                              let bar_el = barend_rec el map in
                              TmIfBz(bar_cond, bar_th, bar_el)

    | TmIfBe(cond, th, el) -> let bar_cond = barend_rec cond map in
                              let bar_th = barend_rec th map in
                              let bar_el = barend_rec el map in
                              TmIfBe(bar_cond, bar_th, bar_el)
    | _ -> t
  in
  barend_rec t RefVar.empty;;

(*let substitute v ts t =
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
*)

(*Substitue x par a dans l*)
let instantie l x a = 
  let rec inst_rec l' = match l' with

    TmVar(v) as tv -> if v = x then a else tv
    | TmAbs(name, term) ->  TmAbs(name,(inst_rec term))
    | TmApp(t1, t2) ->  TmApp((inst_rec t1), (inst_rec t2))
    | TmLet(name, t1, t2) -> TmLet(name, (inst_rec t1), (inst_rec t2))
    | TmIfBz(cond, th, el) -> TmIfBz((inst_rec cond), (inst_rec th), (inst_rec el))
    | TmIfBe(cond, th, el) -> TmIfBz((inst_rec cond), (inst_rec th), (inst_rec el))
    | TmSeq(seq) -> let rec process suite =
                      match suite with
                      | [] -> []
                      | hd :: tl -> (inst_rec hd) :: (process tl)
                    in TmSeq(process seq)
    | _ -> l'

  in inst_rec l
;;


let rec ltrcbv_etape term = let status = "KO" in
  match term with

    | TmApp(TmAbs(name,body),t2)  -> let inst = instantie body name t2 in
                                    ("OK", inst)

    | TmApp(TmOp(Hd), (TmSeq(seq))) -> let res s = match s with
                                      | [] -> (status,term)
                                      | hd :: tl -> ("OK",hd)
                                      in res seq

    | TmApp(TmOp(Tl), (TmSeq(seq))) ->let _ = print_string "\nhere\n" in
                                      let res s = match s with
                                      | [] -> (status,term)
                                      | hd :: tl -> ("OK",TmSeq(tl))
                                      in res seq

    | TmApp(TmOp(Fixpoint), TmAbs(name, body)) as app ->
                        let inst = instantie (barendregt body) name app in
                          ("OK", inst)
    
    | TmApp(TmApp(TmOp(Add),TmInt(e1)),TmInt(e2)) -> ("OK", TmInt(e1+e2))
    | TmApp(TmApp(TmOp(Sub),TmInt(e1)),TmInt(e2)) -> ("OK", TmInt(e1-e2))
    | TmApp(TmApp(TmOp(Cons),elem),TmSeq(seq)) -> ("OK", TmSeq(elem::seq))

    | TmApp(t1, t2) ->  let (status,resfun) = ltrcbv_etape t1 in
                        if status = "OK" then ("OK",TmApp(resfun, t2))
                        else
                          let (status,resarg) = ltrcbv_etape t2 in
                          if status = "OK" then ("OK",TmApp(t1, resarg))
                          else ltrcbv_etape t1

    | TmLet(name, t1, t2) -> let (status,resfun) = ltrcbv_etape t1 in
                        if status = "OK" then ("OK",TmLet(name, resfun, t2))
                        else
                          let inst = instantie t2 name t1 in
                          ("OK",inst)

    | TmIfBz(cond, th, el) -> let (status,resfun) = ltrcbv_etape cond in
                        if status = "OK" then ("OK", TmIfBz(resfun, th, el))
                        else
                          if cond = TmInt(0) then ("OK", th)
                          else ("OK", el)

    | TmIfBe(cond, th, el) -> let (status,resfun) = ltrcbv_etape cond in
                        if status = "OK" then ("OK", TmIfBe(resfun, th, el))
                        else
                          if cond = TmSeq([]) then ("OK", th)
                          else ("OK", el)

    | TmSeq(seq) -> let rec process suite pre =
                      match suite with
                      | [] -> (status,term)
                      | hd :: tl -> let (status,resfun) = ltrcbv_etape hd in
                          if status = "OK" then 
                            ("OK", TmSeq(pre @ (resfun::tl)))
                          else
                            process tl (pre @ [hd])
                    in process seq []

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
    if (!c) = (!max_eval) then print_string "\nSTOP trop de reductions\n" else ()
  with
    BreakLoop -> print_string "\névaluation terminée\n"
;;

(* OK !
ltrcbv ex_id
ltrcbv ex_kiom
ltrcbv ex_s
ltrcbv delta
ltrcbv ex_triple
ltrcbv ex_siii

ltrcbv ex_2p3 
ltrcbv ex_plus23
ltrcbv ex_moins23

ltrcbv ex_seq123
ltrcbv ex_enseq3
ltrcbv ex_enseq2d4
ltrcbv ex_seq3i
ltrcbv ex_cons123
ltrcbv ex_izte23a0
ltrcbv ex_izte23a8
ltrcbv ex_iete23ae
ltrcbv ex_iete23a123

ltrcbv ex_plusun
ltrcbv ex_letplus
ltrcbv letTerm

ltrcbv ex_letii3
ltrcbv ex_sum10 -> trace baleze (origine inconnue)
*)

(* ECHEC 
Probleme avec point fixe OU mauvaise gestions 
des listes Hd et Tl dans ltrcbv_etape

ltrcbv ex_mapp123 
ltrcbv (TmApp(ex_map, ex_plusun)) ??
*)