type exp =
  | Var of int
  | One
  | Abs of exp
  | App of exp * exp
  | Sub of exp * subst
and subst =
  | Up
  | Id
  | Compose of subst * subst
  | Ext of subst * exp

type ty =
  | Unit
  | Arr of ty * ty

type ctx = ty list

type nf =
  | One
  | Abs of nf
  | Ne of ne
and ne =
  | Var of int
  | App of ne * nf

val nbe : ty -> ctx -> exp -> nf
