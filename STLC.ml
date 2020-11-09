

(*constantes et generateur*)
let max_unif = ref 1000;;
let cnt_tvar = ref 0;;
let fresh_tvar () = incr cnt_tvar; "T"^(string_of_int !cnt_tvar);;

let rec pretty_printer_type t =
  match t with
    TyInt -> "int"
  | TyVar(x) -> x
  | TyFun(t1,t2) -> let t1' = pretty_printer_type t1 in
                    let t2' = pretty_printer_type t2 in
                    let res = "("^t1'^") → "^t2' in res
  | TyList(t) -> "["^(pretty_printer_type t)^"]"
  | TyForall(TyVar(x),t) -> "∀"^x^"."^(pretty_printer_type t)
  | _ -> ""
;;


let statusToString sts = match sts with
  Fini -> "Fini"
  | Continue -> "continue"
  | Echec -> "echec"
  | Recommence -> "recommence"

let opToString op = match op with
    Add -> "+"
  | Sub -> "-"
  | Hd -> "hd"
  | Tl -> "tl"
  | Cons -> "::"
  | Fixpoint -> "fxp"

let rec pretty_printer_term t =
  match t with
   TmInt(v) -> string_of_int v
  | TmVar(v) -> v
  | TmAbs(name,t) ->
                         let t = pretty_printer_term t in
                         "λ"^name^"."^t
  | TmApp(TmOp(op) as t1,t2) -> (pretty_printer_term t2)^" "^(pretty_printer_term t1)
  | TmApp(t1,t2) -> "("^(pretty_printer_term t1)^" "^(pretty_printer_term t2)^")"
  | TmOp(op) -> opToString op
  | TmSeq(seq) -> pretty_print_list seq
  | TmIfBz(body,t,e) -> let bodystr = pretty_printer_term body in
                        let thenstr = pretty_printer_term t in
                        let elsestr = pretty_printer_term e in
                        "(if0 "^bodystr^" then "^thenstr^" else )"^elsestr
  | TmIfBe(body,t,e) -> let bodystr = pretty_printer_term body in
                        let thenstr = pretty_printer_term t in
                        let elsestr = pretty_printer_term e in
                        "(ifempty "^bodystr^" then "^thenstr^" else )"^elsestr
  | TmLet(var,e1,e2) -> let e1str = pretty_printer_term e1 in
                        let e2str = pretty_printer_term e2 in
                        "let "^var^" = "^e1str^" in "^e2str

and pretty_print_list l =
  let rec build l = match l with
    [] -> "]"
    |(x::xs) -> (pretty_printer_term x)^" "^(build xs) in
  "[ "^build l
;;

let pretty_printer_equas equas = match equas with
    Equa(t1,t2) -> "\nequation : ["^(pretty_printer_type t1)^","^(pretty_printer_type t2)^"] "
  | _ -> "error"


let occur_check name typ =
  let rec occur_rec t = match t with
      TyInt -> false
    | TyVar(x) -> x=name
    | TyFun(t1,t2) -> occur_rec t1 || occur_rec t2
    | TyList(t) -> occur_rec t
    | TyForall(arg,res) -> occur_rec res
  in
  occur_rec typ
;;

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


let substitute_everywhere v ts equs =
  List.map (function el -> match el with
                              Equa(t1,t2) ->
                              Equa(substitute v ts t1,substitute v ts t2) | e -> e)
      equs
;;
  
let remove_l l nth = let length = List.length l in
  let last_el = List.nth l (length-1) in
  let rec rem_rec l' n = match l',n with
      [],_ -> raise BadAccess
    | (x::xs),n -> if n = nth then let new_l = last_el :: xs in List.rev (List.tl (List.rev new_l)) (*très sale mais a ce stade j'ai plus le temps de passer sur des tableaux et des access constant*)
                    else x :: (rem_rec xs (n+1))
  in
  rem_rec l 0;;
  


let genEquaOp op target = match op with
  Add -> Equa(target,TyFun(TyInt,TyFun(TyInt,TyInt)))
  | Sub -> Equa(target,TyFun(TyInt,TyFun(TyInt,TyInt)))
  | Hd -> let tvar = fresh_tvar () in
            Equa(target,TyForall(TyVar tvar,TyFun(TyList(TyVar tvar),TyVar tvar)))
  | Tl -> let tvar = fresh_tvar () in
            Equa(target,TyForall(TyVar tvar,TyFun(TyList(TyVar tvar),TyList(TyVar tvar))))
  | Cons -> let tvar = fresh_tvar () in 
            let new_type = TyForall(TyVar tvar,
                            TyFun(TyVar(tvar),
                              TyFun(TyList(TyVar(tvar)),
                                TyList(TyVar(tvar))))) in
            Equa(target,new_type)
  | Fixpoint -> ErroratStep "generation d'equation pour point fixe non pris en charge"
;;

(*retrouve le type guess qui a servit d'initiateur a l'inférence, et retourne le type a coté, qui est le bon type inféré*)
let cut_the_guess equas =
  let rec cut_rec eqs = match eqs with
      [] -> raise GuessNotFound
    | Equa(TyVar("???"),td) :: xs -> td
    | Equa(tg,TyVar("???")) :: xs -> tg
    | (x::xs) -> cut_rec xs in
  cut_rec equas
;;

let barendregtisation t =
  let rec barendrec t ctx = match t with
    TyFun(arg,res) -> let baren_arg  = barendrec arg ctx in
                      let baren_res = barendrec res ctx in
                      TyFun(baren_arg,baren_res)
    | TyVar(x) as var -> let res = Typecontext.find_opt x ctx in
             let check v = match v with
                 Some (name) -> TyVar(name)
               | None -> var
             in check res
    | TyInt -> t
    | TyList(t) -> TyList(barendrec t ctx)
    | TyForall(TyVar(arg),res) -> let tvar = fresh_tvar () in
                            let new_ctx = Typecontext.add arg tvar ctx in
                            TyForall(TyVar(tvar),barendrec res new_ctx)
    | _ -> t
  in
  barendrec t (Typecontext.empty)
;;    


let unification_step equs step =
  let length = List.length equs in
  if step >= length then (equs,Fini)
  else
    let el = List.nth equs step in
    match el with
      Equa(TyVar("???"),_) -> (equs,Continue)
      |Equa(_,TyVar("???")) -> (equs,Continue)
      |Equa(t1,t2) when (t1 = t2) -> (remove_l equs step,Continue)
      |Equa(TyFun(tga,tgr),TyFun(tda,tdr)) -> let new_equs = remove_l equs step in
                                             let eq1 = Equa(tga,tda) in
                                             let eq2 = Equa(tgr,tdr) in

                                             (new_equs@(eq1 ::(eq2 :: [])),Recommence)
      |Equa(TyVar(name),td) -> if not (occur_check name td) then
                                let new_equs = remove_l equs step in
                                (substitute_everywhere name td new_equs,Recommence)
                              else
                                (ErroratStep("error at step :"^(string_of_int step)) :: equs,Echec)
      |Equa(tg,TyVar(name)) -> if not (occur_check name tg) then
                                let new_equs = remove_l equs step in
                                (substitute_everywhere name tg new_equs,Recommence)
                              else
                                (ErroratStep("error at step :"^(string_of_int step)) :: equs,Echec)
      |Equa(TyForall(var,res),td) -> let typ1 = barendregtisation (TyForall(var,res)) in
                                     let rs x = match x with
                                      TyForall(v,r) -> r
                                      | _ -> x in
                                     let eq1 = Equa((rs typ1),td) in
                                     let new_equs = remove_l equs step in
                                     (new_equs@(eq1::[]),Recommence)
      |Equa(tg,TyForall(var,res)) -> let typ1 = barendregtisation (TyForall(var,res)) in
                                     let rs x = match x with
                                      TyForall(v,r) -> r
                                      | _ -> x in
                                     let eq1 = Equa((rs typ1),tg) in
                                     let new_equs = remove_l equs step in
                                     (new_equs@(eq1::[]),Recommence)
      |Equa(TyList(t1),TyList(t2)) -> let new_equs = remove_l equs step in
                                      let eq1 = Equa(t1,t2) in
                                      (new_equs@(eq1 :: []),Recommence)
      
      | _ -> (ErroratStep("error at step :"^(string_of_int step)) :: equs ,Echec)
;;

let remove_var var vars =
  let rec remove_rec vs = match vs with
    [] -> vs
    |(x::xs) -> if x = var then
                  remove_rec xs
                else
                  x :: (remove_rec xs)
    in
    remove_rec vars
;;

let free_var typ = 
  let rec free_rec t freeset = match t with
    TyFun(arg,res) -> let freearg = SS.of_list (free_rec arg freeset) in
                      let freeres = SS.of_list (free_rec res freeset) in
                      SS.elements (SS.union freearg freeres)

    | TyVar(name) -> (name :: freeset)
    | TyInt -> freeset
    | TyList(t') -> free_rec t' freeset
    | TyForall(TyVar(var),res) -> let freeres = free_rec res freeset in
                          remove_var var freeres 
    | _ -> raise CtorTypeNotSupported in
    free_rec typ []
;;

let generalise typ = let freeOfType = free_var typ in
  let rec generalise_rec frees generalised = match frees with
    [] -> generalised
    | (freevar::xs) -> generalise_rec xs (TyForall(TyVar(freevar),generalised)) in
  generalise_rec freeOfType typ 
;;

let rec gen_equas ctx trm target =
  let equas = [] in
  match trm with
    TmInt(n) -> (Equa(target,TyInt)) :: equas
  | TmVar(x) -> let typevar = Typecontext.find_opt x ctx in
             let checktype t = match t with
                 Some (typ) -> (Equa(typ,target)) :: equas
               | None -> (ErroratStep("Var:"^x^" does not have a type in that context")) :: equas  in
             checktype typevar
  | TmAbs(name,body) -> let ta = fresh_tvar () in
                          let tr = fresh_tvar () in
                          let new_ctx = Typecontext.add name (TyVar(ta)) ctx in
                          let equ_body = gen_equas new_ctx body (TyVar(tr)) in
                          let new_equas = (Equa(target,TyFun(TyVar(ta),TyVar(tr)))) :: equas in
                          List.append equ_body new_equas
  | TmApp(term1,term2) -> let ta = fresh_tvar () in
                          let equ_fun = gen_equas ctx term1 (TyFun(TyVar(ta),target)) in
                          let equ_arg = gen_equas ctx term2 (TyVar(ta)) in
                          List.append equ_fun equ_arg
  | TmOp(op) -> (genEquaOp op target) :: equas
  | TmSeq(seq) -> genEquaSeq seq target ctx
  | TmIfBz(cond,th,el) -> let nt = fresh_tvar () in
                          let condEqua = gen_equas ctx cond TyInt in
                          let thEqua = gen_equas ctx th (TyVar(nt)) in
                          let elEqua = gen_equas ctx el (TyVar(nt)) in
                          let eqs1 = condEqua @ (thEqua @ elEqua) in
                          eqs1@(Equa(target,TyVar(nt)) :: [])
  | TmIfBe(cond,th,el) -> let tvar = fresh_tvar () in
                          let nt = fresh_tvar () in
                          let condEqua = gen_equas ctx cond (TyList(TyVar(tvar))) in
                          let thEqua = gen_equas ctx th (TyVar(nt)) in
                          let elEqua = gen_equas ctx el (TyVar(nt)) in
                          let eqs1 = condEqua @ (thEqua @ elEqua) in
                          eqs1@(Equa(target,TyVar(nt)) :: [])
  | TmLet(var,e1,e2) -> let (typeOfe1,status) = type_inference e1 ctx in
                          let generalised = generalise typeOfe1 in
                          let new_ctx = Typecontext.add var generalised ctx in
                          let equae2 = gen_equas new_ctx e2 target in equae2

and genEquaSeq seq target ctx = 
let tvar = fresh_tvar () in
let equas = (Equa(target, TyList(TyVar tvar)) :: []) in
let rec gen_rec xs equels = match xs with
  [] -> equels
  | (el::els) -> let equel = gen_equas ctx el (TyVar tvar) in
                    gen_rec els (equels @ equel) in
  gen_rec seq equas

and unification equs =
  let new_equs = ref equs in
  let c = ref 0 in
  let step = ref 0 in
  let status = ref Echec in
  while (!c) < (!max_unif) do
    let (res,stat) = unification_step (!new_equs) (!step) in
    let str_equs = List.map (function eq -> pretty_printer_equas eq) res in
    let () = print_string "[\n" in
    let () = List.iter print_string str_equs in
    let () = print_string (statusToString stat) in
    let () = print_string "\n]" in
    if stat = Continue then
      begin
        new_equs := res;
        incr step
      end
    else
      if stat = Recommence then
        begin
          new_equs := res;
          step := 0
        end
      else
        if stat = Echec then
          begin
            new_equs := res;
            c := !max_unif
          end
        else (* fini *)
          begin
            new_equs := res;
            c := !max_unif (*on l'arrete*)
          end;
    incr c;
    status := stat
  done;
  (!new_equs,!status)



and type_inference term ctx =
  let equations = gen_equas ctx term (TyVar("???")) in
  let str_equs = List.map (function eq -> pretty_printer_equas eq) equations in
  let () = List.iter print_string str_equs in
  let (res,status) = unification equations in
  (*let str_equs = List.map (function eq -> pretty_printer_equas eq) res in
  let () = List.iter print_string str_equs in*)
  if status = Fini then let typ = (cut_the_guess res) in (typ,status)
  else raise (TypingFail ("Echec de typage pour le terme : "^(pretty_printer_term term)))

;;

let emptyContext = Typecontext.empty;;

let typer term = let (typ,status) = type_inference term emptyContext in
  (pretty_printer_term term)^" : "^(pretty_printer_type typ)


(* Fonction de creation de terme fastidieux *)

let cons o1 o2 = TmApp(TmApp(TmOp(Cons),o1),o2);;
let add o1 o2 = TmApp(TmApp(TmOp(Add),o1),o2);;
let nil = TmSeq([])

(*------------------------TESTs-----------------------------------------*)




(*Test pour itération 1/2*)
let ex_id = TmAbs("x",TmVar("x"));; (*ok*)
let ex_k = TmAbs("x",TmAbs("y",TmVar("x")));; (*ok*)
let ex_a = TmAbs("x",TmAbs("y",TmApp(TmVar("x"),TmVar("y"))));; (*ok*)
(*ok*)
let ex_s = TmAbs( "x" , TmAbs ( "y" , TmAbs ( "z", TmApp ( TmApp (TmVar "x" , TmVar "z" ) , TmApp (TmVar "y",TmVar "z") ) )));;
let ex_skk = TmApp(TmApp(ex_s,ex_k),ex_k);; (*ok*)
let delta = TmAbs ( "x" , TmApp (TmVar "x" , TmVar "x" ));;
let ex_om = TmApp(delta,delta);; (*ok*)
let ex_kiom = TmApp(TmApp(ex_k,ex_id),ex_om);; (*ok*)
let ex_triple = TmAbs("x",TmApp(TmApp(TmVar("x"),TmVar("x")),TmVar("x")));; (*ok*)
let ex_siii = TmApp(TmApp(TmApp(ex_s,ex_id),ex_id),ex_id);; (*ok*)


(*Test pour itération 3*)
let ex_2p3 = TmApp(TmApp(TmOp(Add),TmInt(7)),TmInt(7));;  (*ok*)
let ex_plus = TmAbs("x",TmAbs("y",TmApp(TmApp(TmOp(Add),TmVar("x")),TmVar("y"))));; (*ok*)
let ex_plus23 = TmApp(TmApp(ex_plus,TmInt(2)),TmInt(7));; (*ok*)
let ex_moins = TmAbs("x",TmAbs("y",TmApp(TmApp(TmOp(Sub),TmVar("x")),TmVar("y"))));; (*ok*)
let ex_moins23 = TmApp(TmApp(ex_moins,TmInt(2)),TmInt(3));; (*ok*)
let ex_moins32 = TmApp(TmApp(ex_moins,TmInt(3)),TmInt(2));; (*ok*)
let ex_seq123 = TmSeq([TmInt(1);TmInt(2);TmInt(3)]) (*ok*)
let ex_enseq3 = TmAbs("x",TmSeq([TmVar("x");TmVar("x");TmVar("x")]));; (*ok*)
let ex_enseq2d4 = TmAbs("x",TmAbs("y",TmSeq([TmVar("x");TmVar("y");TmVar("x");TmVar("y")])));; (*ok*)
let ex_seq3i = TmApp(ex_enseq3,ex_id);; (*ok*)
let ex_enseq2d = TmApp(TmApp(ex_enseq2d4,ex_id),TmInt(8));; (*ne passe pas car type pas uniforme, normal*)

let ex_cons123 = cons (TmInt(1)) (cons (TmInt(2)) (cons (TmInt(3)) nil));; (*ok*)
let ex_izte23a0 = TmIfBz(TmInt(0), TmInt(2), TmInt(3));; (*ok*)
let ex_izte23a8 = TmIfBz(TmInt(8), TmInt(2), TmInt(3));; (*ok*)
let ex_iete23ae = TmIfBe(nil, TmInt(2), TmInt(3));; (*ok*)
let ex_iete23a123 = TmIfBe(ex_seq123,TmInt(3),TmInt(6));;(*ok*)
(*ok*)
let letTerm = TmLet("x",ex_2p3,TmApp(TmAbs("x",TmApp(TmApp(TmOp(Add),TmVar("x")),TmInt(7))),TmVar("x")));;

let ex_plusun = TmAbs("x",add (TmVar("x")) (TmInt(1)));;
let ex_letplus = TmLet("x", (add (TmInt(2)) (TmInt(3))),(TmApp(ex_plusun, TmVar("x"))));;
let ex_letii3 = TmLet("f", TmAbs("x", TmVar("x")),TmApp(TmApp(TmVar("f"), TmVar("f")), TmInt(3)));;

(*Test pour itération 4*)

(*let ex_sum = cfix("sum", clam("x", cizte(cvar("x"), cint(0), cadd(cvar("x"), capp(cvar("sum"), csub(cvar("x"), cint(1)))))))
let ex_sum10 = capp(ex_sum, cint(10))

let ex_letletmap = clet("x", cadd(cint(2), cint(3)), (* let x = 2 + 3 in let y = ^z.y + z in map y [1, 2, 3]*)
  clet("y", clam("z", cadd(cvar("x"), cvar("z"))),
    capp(capp(ex_map, cvar("y")), ex_seq123)))*)















