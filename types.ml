type ttype =
  TyFun of ttype * ttype
| TyVar of string 
| TyInt
| TyList of ttype
| TyForall of string * ttype
| TyUnit
| TyRef of ttype
| TyWV of string * ttype * bool
| TyWF of string * ttype * bool

type op = 
    Add
  | Sub
  | Hd (*head of list*)
  | Tl (*tail of list*)
  | Cons (*:: of list*)
  | Fixpoint (*operateur de point fixe*)
  | Deref
  | Ref
  | Assign


and term =
  TmVar of string (*nom de la variable*)
| TmAbs of string * term
| TmApp of term * term
| TmInt of int
| TmOp of op
| TmSeq of term list
| TmIfBz of term * term * term
| TmIfBe of term * term * term
| TmLet of string * term * term
| TmReg of string
| TmUnit
;;

type status =
  Fini
| Continue
| Echec
| Recommence

type tequa =
  Equa of ttype * ttype
|ErroratStep of string
;;

module Typecontext = Map.Make(String)
module SS = Set.Make(String)

type ('a, 'b) either = Ok of 'a | Error of 'b;;
type typeError =
  UnboundVariable of string
| AppWrongArgumentType of term * ttype * term * ttype
| AppNotFunction of term * ttype;;


exception BadAccess;;
exception GuessNotFound;;
exception CtorTypeNotSupported;;
exception TypingFail of string ;;
exception BreakLoop;;
