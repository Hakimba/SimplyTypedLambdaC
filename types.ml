type ttype =
  TyFun of ttype * ttype
| TyVar of string (*variable de type, non polymorphique*)
| TyInt
| TyList of ttype
| TyForall of ttype * ttype

type op = 
    Add
  | Sub
  | Hd (*head of list*)
  | Tl (*tail of list*)
  | Fixpoint (*operateur de point fixe*)

type llist =
  Nil
  | Cons of term * llist

and term =
  TmVar of string (*nom de la variable*)
| TmAbs of string * term
| TmApp of term * term
| TmInt of int
| TmOp of op
| TmList of llist
| TmIfBz of term * term * term
| TmIfBe of term * term * term
| TmLet of string * term * term
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
