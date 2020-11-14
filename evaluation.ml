

let cnt_terme = ref 0;;
let cnt_addr = ref 0;;
let max_eval = ref 1000;;
module RefVar = Map.Make (String);;
module Memory = Map.Make (String);;

let fresh_tvar () =
  incr cnt_terme;
  "t"^(string_of_int !cnt_terme)
;;

let fresh_addr () =
  incr cnt_addr;
  "a"^(string_of_int !cnt_addr)
;;

let barendregt (t:term) =
  let rec barend_rec t map =
    match t with

    | TmVar(v) ->
                  let res = try
                    TmVar((RefVar.find v map))
                  with
                    Not_found -> TmVar(v)
                  in res

    | TmAbs(name, term) -> 
                            let new_v = fresh_tvar() in
                            let new_m = RefVar.add name new_v map in
                            TmAbs(new_v, barend_rec term new_m)

    | TmApp(t1, t2) -> let barendt1 = barend_rec t1 map in
                        let barendt2 = barend_rec t2 map in
                      TmApp(barendt1, barendt2)

    | TmSeq(seq) ->  let rec seqBarend l = 
                        match l with
                          [] -> []
                        | (x::xs) -> ((barend_rec x map) :: (seqBarend xs))
                      in TmSeq(seqBarend seq)
    | TmIfBz(cond,e1,e2) -> let cond_ = barend_rec cond map in
                            let e1_ = barend_rec e1 map in
                            let e2_ = barend_rec e2 map in
                        TmIfBz(cond_,e1_,e2_)
    | TmIfBe(cond,e1,e2) -> let cond_ = barend_rec cond map in
                            let e1_ = barend_rec e1 map in
                            let e2_ = barend_rec e2 map in
                        TmIfBe(cond_,e1_,e2_)
    | TmLet(name,e1,e2) -> let new_v = fresh_tvar () in
                            let l1 = barend_rec e1 map in
                            let new_map = RefVar.add name new_v map in
                            let l2 = barend_rec e2 new_map in
                            TmLet(new_v,l1,l2)
    | _ -> t
  in
  barend_rec t RefVar.empty;;

(*Substitue x par a dans l*)
let instantie l x a = 
  let rec inst_rec l' = match l' with
    TmVar(v) as tv -> if v = x then a else tv

    | TmAbs(name, term) -> TmAbs(name,(inst_rec term))

    | TmApp(t1, t2) -> TmApp((inst_rec t1), (inst_rec t2))
    | TmIfBz(cond,e1,e2) -> let cond_ = inst_rec cond in
                            let e1_ = inst_rec e1 in
                            let e2_ = inst_rec e2 in
                            TmIfBz(cond_,e1_,e2_)
    | TmIfBe(cond,e1,e2) -> let cond_ = inst_rec cond in
                            let e1_ = inst_rec e1 in
                            let e2_ = inst_rec e2 in
                            TmIfBe(cond_,e1_,e2_)
    | TmLet(name,e1,e2) ->
                            let e1_ = inst_rec e1 in
                            let e2_ = inst_rec e2 in
                            TmLet(name,e1_,e2_)
    | TmSeq(seq) -> let rec inst_seq_rec l = 
                      match l with
                        [] -> []
                        | (x::xs) -> (inst_rec x) :: (inst_seq_rec xs) in
                    TmSeq((inst_seq_rec seq))

    | TmOp(_) -> l'
    | TmInt(_) -> l'
    | TmReg(_) -> l'
    | TmUnit -> l'
      in inst_rec l
;;


let rec ltrcbv_etape term mem = let status = "KO" in
  match term with
     TmSeq(seq) -> let rec seq_ltrcbv l new_status = 
                      match l with
                        [] -> ([],new_status)
                        | (x::xs) -> let (status,resel,_) = ltrcbv_etape x mem in
                                      if status = "OK" then
                                        ((resel :: xs),"OK")
                                      else
                                        let (els,sts) = (seq_ltrcbv xs new_status) in
                                        ((x::els),sts)

                      in
                      let (ress,s) = seq_ltrcbv seq "KO" in (s,TmSeq(ress),mem)
    | TmApp(TmOp(Hd),TmSeq(seq)) -> let len = List.length seq in
                                    if len > 0 then
                                      ("OK",(List.hd seq),mem)
                                    else
                                      raise (Failure "hd")

    | TmApp(TmOp(Tl),TmSeq(seq)) -> let len = List.length seq in
                                    if len > 0 then
                                      ("OK",TmSeq(List.tl seq),mem)
                                    else
                                      raise (Failure "tail")

    | TmApp(TmOp(Fixpoint),TmAbs(name,t1)) -> let res = (instantie (barendregt t1) name term) in
                                              ("OK",res,mem)

    | TmApp(TmOp(Ref),t2) -> let taddr = fresh_addr () in
                                      let res = TmReg(taddr) in
                                      let new_mem = Memory.add taddr t2 mem in
                                      ("OK",res,new_mem)

    | TmApp(TmOp(Deref),TmReg(addr)) -> let v = (Memory.find addr mem) in
                                        ("OK",v,mem)
    | TmApp(TmApp(TmOp(Add),TmInt(n1)),TmInt(n2)) -> let res = TmInt(n1+n2) in ("OK",res,mem)
    | TmApp(TmApp(TmOp(Sub),TmInt(n1)),TmInt(n2)) -> let res = TmInt(n1-n2) in ("OK",res,mem)
    | TmApp(TmApp(TmOp(Cons),t2),TmSeq(seq)) -> let res = TmSeq((t2 :: seq)) in
                                                ("OK",res,mem)
    | TmApp(TmApp(TmOp(Assign),TmReg(addr)),t3) -> let (_,t3_res,_) = ltrcbv_etape t3 mem in
                                                    let new_mem = Memory.add addr t3_res mem in
                                                    ("OK",TmUnit,new_mem)

    | TmApp(TmAbs(name,body),t2) -> 
                                    let (status,resarg,m) = ltrcbv_etape t2 mem in
                                    if status = "OK" then 
                                      ("OK",(TmApp(TmAbs(name,body),resarg)),m)
                                    else
                                      let inst = instantie body name t2 in
                                      ("OK",inst,mem)
    | TmApp(t1, t2) -> 
                        let (status,resfun,m) = ltrcbv_etape t1 mem in
                        if status = "OK" then("OK",TmApp(resfun,t2),mem)
                        else
                          let (status,resarg,m) = ltrcbv_etape t2 mem in
                          if status = "OK" then ("OK",TmApp(t1,resarg),mem)
                          else ltrcbv_etape t1 mem
    | TmLet(name,e1,e2) -> let (status,resfun,new_mem) = ltrcbv_etape e1 mem in
                            if status = "OK" then
                              let res = TmLet(name,resfun,e2) in
                              ("OK",res,new_mem)
                            else
                              let res = instantie e2 name e1 in
                              ("OK",res,mem)
    | TmIfBz(TmInt(v) as cond ,e1,e2) -> let (status,resfun,new_mem) = ltrcbv_etape cond mem in
                            if status = "OK" then
                              let res = TmIfBz(resfun,e1,e2) in
                              ("OK",res,mem)
                            else
                              if v = 0 then
                                ("OK",e1,mem)
                              else
                                ("OK",e2,mem)
    | TmIfBe(TmSeq(seq) as cond,e1,e2) -> let (status,resfun,new_mem) = ltrcbv_etape cond mem in
                            if status = "OK" then
                              let res = TmIfBe(resfun,e1,e2) in
                              ("OK",res,mem)
                            else
                              let len = List.length seq in
                                if len = 0 then
                                  ("OK",e1,mem)
                                else
                                  ("OK",e2,mem)

    | _ -> (status,term,mem)

let ltrcbv t =
  let courant = ref (barendregt t) in
  let c = ref 0 in
  let mem = ref Memory.empty in
  let _ = print_string (pretty_printer_term (!courant)) in
  try
    while (!c) < (!max_eval) do
      let (status,new_red,new_mem) = ltrcbv_etape (!courant) (!mem) in
      if status = "KO" then raise BreakLoop
      else
        print_string ("\n -> "^(pretty_printer_term new_red));
      courant := new_red;
      mem := new_mem;
      incr c
    done;
    if (!c) = (!max_eval) then print_string "\nSTOP trop de reductions" else ()
  with
    BreakLoop -> print_string "\névaluation terminée"
