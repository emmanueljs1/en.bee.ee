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

type domain =
  | Closure of exp * env
  | Reflect of ty * domain_ne
  | One
and domain_ne =
  | Level of int
  | App of domain_ne * domain_nf
and domain_nf =
  | Reify of ty * domain
and env = domain list

let rec apply (f : domain) (a : domain) : domain =
  match f with
  | Closure (t , rho) -> eval t (a :: rho)
  | Reflect (Arr (ty0 , ty1), e) -> Reflect (ty0 , (App (e , Reify (ty1 , a))))
  | _ -> failwith "bad"
and eval (t : exp) (rho : env) : domain =
  match t with
  | One -> One
  | Var x -> List.nth rho x
  | Abs t -> Closure (t , rho)
  | App (r , s) -> apply (eval r rho) (eval s rho)
  | Sub (t , sigma) -> sub sigma rho |> eval t
and sub (sigma : subst) (rho : env) : env =
  match sigma with
  | Up ->
      begin match rho with
      | _ :: rho' -> rho'
      | _ -> failwith "bad"
      end
  | Id -> rho
  | Compose (sigma, tau) -> sub tau rho |> sub sigma
  | Ext (sigma , s) -> eval s rho :: sub sigma rho

type nf =
  | One
  | Abs of nf
  | Ne of ne
and ne =
  | Var of int
  | App of ne * nf

let rec readback_nf (n : int) (d : domain_nf) : nf =
  match d with
  | Reify (Unit , One) -> One
  | Reify (Arr (ty0 , ty1) , f) ->
      let a = apply f (Reflect (ty0 , Level n)) in
      Abs (readback_nf (n + 1) (Reify (ty1 , a)))
  | Reify (Unit , Reflect (Unit , e)) -> Ne (readback_ne n e)
  | _ -> failwith "bad"
and readback_ne (n : int) (e : domain_ne) : ne =
  match e with
  | Level k -> Var (n - (k + 1))
  | App (e , d) -> App (readback_ne n e , readback_nf n d)

let rec init (gamma : ctx) : env =
  match gamma with
  | [] -> []
  | ty :: gamma -> Reflect (ty , Level (List.length gamma)) :: init gamma

let nbe (ty : ty) (gamma : ctx) (t : exp) : nf =
  let env = init gamma in
  let a = eval t env in
  let n = List.length gamma in
  readback_nf n (Reify (ty , a))
