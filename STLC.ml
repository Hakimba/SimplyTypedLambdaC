open Types


(*constantes et generateur*)
let max_unif = ref 10;;
let cnt_tvar = ref 0;;
let fresh_tvar () = incr cnt_tvar; "T"^(string_of_int !cnt_tvar);;

let rec pretty_printer_type t =
  match t with
    TyInt -> "int"
  | TyVar(x) -> x
  | TyFun(t1,t2) -> let t1' = pretty_printer_type t1 in
                    let t2' = pretty_printer_type t2 in
                    let res = "("^t1'^" -> "^t2'^")" in res
  | TyList(t) -> "["^(pretty_printer_type t)^"]"
  | TyForall(TyVar(x),t) -> "∀"^x^"."^(pretty_printer_type t)
  | _ -> ""
;;

let opToString op = match op with
    Add -> "+"
  | Sub -> "-"
  | Hd -> "hd"
  | Tl -> "tl"
  | Fixpoint -> "fxp"

let rec pretty_printer_term t =
  match t with
   TmInt(v) -> string_of_int v
  | TmVar(v) -> v
  | TmAbs(name,t) ->
                         let t = pretty_printer_term t in
                         "λ"^name^"."^t
  | TmApp(t1,t2) -> (pretty_printer_term t1)^" "^(pretty_printer_term t2)
  | TmUniOp(op,arg) -> let opstr = opToString op in opstr ^ (pretty_printer_term arg)
  | TmBinOp(op,arg1,arg2) -> let opstr = opToString op in
                              let arg1str = pretty_printer_term arg1 in
                              let arg2str = pretty_printer_term arg2 in
                              opstr ^ arg1str ^ arg2str
  | TmList(xs) -> pretty_print_llist xs
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

and pretty_print_llist l =
  let rec build l = match l with
    Nil -> "]"
    | Cons(x,xs) -> (pretty_printer_term x) ^ (build xs) in
  "["^build l
;;

let pretty_printer_equas equas = match equas with
    Equa(t1,t2) -> "equation : ["^(pretty_printer_type t1)^","^(pretty_printer_type t2)^"] "
  | _ -> ""


let occur_check name typ =
  let rec occur_rec t = match t with
      TyInt -> false
    | TyVar(x) -> x=name
    | TyFun(t1,t2) -> occur_rec t1 || occur_rec t2 in
  occur_rec typ
;;

let substitute v ts t =
  let rec sub_rec t = match t with
      (TyVar x) -> if x = v then ts else t
    | TyFun(t1,t2) -> let rt1 = sub_rec t1 in
                      let rt2 = sub_rec t2 in
                      TyFun(rt1,rt2)
  in sub_rec t
;;


let substitute_everywhere v ts equs =
  List.map (function el -> match el with
                              Equa(t1,t2) ->
                              Equa(substitute v ts t1,substitute v ts t2) | e -> e)
      equs
;;
  
let remove_l l nth =
  let rec rem_rec l n = match l,n with
      [],_ -> raise BadAccess
    | (x::xs),n -> if n = nth then xs
                    else x :: (rem_rec xs (n+1))
  in
  rem_rec l 0;;
  


let genEquaOp op target = match op with
  Add -> Equa(target,TyFun(TyFun(TyInt,TyInt),TyInt))
  | Sub -> Equa(target,TyFun(TyFun(TyInt,TyInt),TyInt))
  | Hd -> let tvar = fresh_tvar () in
            Equa(target,TyForall(TyVar tvar,TyFun(TyList(TyVar tvar),TyVar tvar)))
  | Tl -> let tvar = fresh_tvar () in
            Equa(target,TyForall(TyVar tvar,TyFun(TyList(TyVar tvar),TyList(TyVar tvar))))
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
      |Equa(TyFun(tga,tgr),TyFun(tda,tdr)) -> let new_equs = remove_l equs step in
                                             let eq1 = Equa(tga,tda) in
                                             let eq2 = Equa(tgr,tdr) in
                                             
                                             (new_equs@(eq1 ::(eq2 :: [])),Recommence)
      |Equa(tg,TyVar(name)) -> if not (occur_check name tg) then
                                let new_equs = remove_l equs step in
                                (substitute_everywhere name tg new_equs,Recommence)
                              else
                                (ErroratStep("error at step :"^(string_of_int step)) :: equs,Echec)
      |Equa(TyVar(name),td) -> if not (occur_check name td) then
                                let new_equs = remove_l equs step in
                                (substitute_everywhere name td new_equs,Recommence)
                              else
                                (ErroratStep("error at step :"^(string_of_int step)) :: equs,Echec)
      |Equa(TyForall(var,res),td) -> let typ1 = barendregtisation res in
                                     let eq1 = Equa(typ1,td) in
                                     let new_equs = remove_l equs step in
                                     (new_equs@(eq1::[]),Recommence)
      |Equa(tg,TyForall(var,res)) -> let typ1 = barendregtisation res in
                                     let eq1 = Equa(typ1,tg) in
                                     let new_equs = remove_l equs step in
                                     (new_equs@(eq1::[]),Recommence)
      |Equa(TyList(t1),TyList(t2)) -> let new_equs = remove_l equs step in
                                      let eq1 = Equa(t1,t2) in
                                      (new_equs@(eq1 :: []),Recommence)
      |Equa(t1,t2) -> if t1 = t2 then
                       (remove_l equs step,Continue)
                     else
                       (ErroratStep("error at step :"^(string_of_int step)) :: equs,Echec)
      
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
    | TyList(t) -> free_rec t freeset
    | TyForall(TyVar(var),res) -> let freeres = free_rec res freeset in
                          remove_var var freeres in
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
  | TmUniOp(op,trm) -> (genEquaOp op target) :: equas
  | TmBinOp(op,term1,term2) -> (genEquaOp op target) :: equas
  | TmList(xs) -> genEquaList xs target ctx
  | TmIfBz(cond,th,el) -> let condEqua = gen_equas ctx cond TyInt in
                          let thEqua = gen_equas ctx th target in
                          let elEqua = gen_equas ctx el target in
                          condEqua @ (thEqua @ elEqua)
  | TmIfBe(cond,th,el) -> let tvar = fresh_tvar () in
                          let condEqua = gen_equas ctx cond (TyForall(TyVar(tvar),TyFun(TyList(TyVar(tvar)),TyVar(tvar)))) in
                          let thEqua = gen_equas ctx th target in
                          let elEqua = gen_equas ctx el target in
                          condEqua @ (thEqua @ elEqua)
  | TmLet(var,e1,e2) -> let (typeOfe1,status) = type_inference e1 ctx in
                          let generalised = generalise typeOfe1 in
                          let new_ctx = Typecontext.add var generalised ctx in
                          let equae2 = gen_equas new_ctx e2 target in equae2

and genEquaList xs target ctx = 
let tvar = fresh_tvar () in
let equas = (Equa(target, TyList(TyVar tvar)) :: []) in
let rec gen_rec xs equels = match xs with
  Nil -> equels
  | Cons(el,els) -> let equel = gen_equas ctx el (TyVar tvar) in
                    gen_rec els (equel @ equels) in
  gen_rec xs equas

and unification equs =
  let new_equs = ref equs in
  let c = ref 0 in
  let step = ref 0 in
  let status = ref Echec in
  while (!c) < (!max_unif) do
    let (res,stat) = unification_step (!new_equs) (!step) in
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
          new_equs := res
        else (* fini *)
          begin
            new_equs := res
          end;
    incr c;
    status := stat
  done;
  (!new_equs,!status)



and type_inference term ctx =
  let equations = gen_equas ctx term (TyVar("???")) in
  (*let str_equs = List.map (function eq -> pretty_printer_equas eq) equations in
  let () = List.iter print_string str_equs in*) 
  let (res,status) = unification equations in
  let (typ,_) = (cut_the_guess res,status) in
  (typ,status)
;;

let emptyContext = Typecontext.empty;;

let typer term = let (typ,status) = type_inference term emptyContext in
  (pretty_printer_type typ,status)

(*Test pour itération 1/2*)
let idIntTerm = TmAbs("x",TmVar "x");; (* /x : Int -> x*)
let idFunTerm = TmAbs("f",TmVar "f");; (* /f : int -> int -> f *)
let idAppTerm = TmApp (idFunTerm,idIntTerm);;
let appFunc = TmAbs("x",TmAbs("y",TmApp(TmVar "x", TmVar "y")));; (* /xy -> x y *)
let s = TmAbs( "x" , TmAbs ( "y" , TmAbs ( "z", TmApp ( TmApp (TmVar "x" , TmVar "z" ) , TmApp (TmVar "y",TmVar "z") ) )));;
let delta = TmAbs ( "x" , TmApp (TmVar "x" , TmVar "x" ));;

(*Test pour itération 3*)
let addTerm = TmBinOp(Add,TmInt(5),TmInt(9));;
let subTerm = TmBinOp(Sub,TmInt(5),TmInt(9));;
(*celui qui suit : match failure*)
let listTerm = TmList(Cons(TmInt(6),Nil));;

let hdIntTerm = TmUniOp(Hd,TmList(Cons(TmInt(6),Nil)));;
let tailIntTerm = TmUniOp(Tl,TmList(Cons(TmInt(8),Cons(TmInt(6),Nil))));;
(*les trois suivant ne marchent pas : match failure*)
let ifbzTerm = TmIfBz(TmInt(0),listTerm,listTerm);;
let ifbeTerm = TmIfBe(TmList(Nil),listTerm,listTerm);;
let letTerm = TmLet("x",TmInt(7),ifbzTerm);;

