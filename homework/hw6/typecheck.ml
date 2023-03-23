open Ast

module Env = Map.Make (String) type env = typ Env.t

exception Type_error of string 
let ty_err msg = raise (Type_error msg)

let todo () = failwith "TODO"

(*Notes:
   1) our abstract semantics only compute the if
the result is of kind integer or list.
   2) We only care about abstract semantics that are
sound so abstract values that overapproximates concrete values
when we evaluate a program under concrete semantics and our 
abstract semantics.
3)Abstract values are the types
4) Type checking: The programmer provides some types (typically,
every variable) and the compiler complains if some types are
inconsistent.*)

(*env is a typing environment which is a mapping from varaibles to types*)
let rec typecheck (env : env) (e : expr) : typ =
  try
  match e with
  | NumLit _ -> TInt

  | Var v -> 
   (if (Env.mem (v) (env))
   then (Env.find (v) (env))
   else ty_err("Error at Variable"))

  | Binop(e1,op,e2) -> 
   (match typecheck (env) (e1) with
   | TInt ->
      (match typecheck (env) (e2) with
      | TInt -> TInt
      | _ -> ty_err("Error at Arithmetic and Binary operations"))
   | type_of_e1 ->
      (if typecheck (env) (e2) = type_of_e1
      then (match op with
            | Eq -> TInt
            | _ -> ty_err("Error at Arithmetic and Binary operations"))
      else ty_err("Error at Arithmetic and Binary operations")))

  | IfThenElse(e1,e2,e3) -> 
   (match typecheck (env) (e1) with
   | TInt ->
      (if typecheck (env) (e2) = typecheck (env) (e3)
      then typecheck (env) (e2)
      else ty_err("Error at IfThenElse"))
   | _ -> ty_err("Error at IfThenElse"))

  | LetBind(strx,t_opt,e1,e2) -> 
   (match t_opt with
   | Some t -> 
      (if (typecheck (env) (e1)) = t
      then typecheck (Env.add (strx) (t) (env)) (e2)
      else ty_err("Error at LetBind"))
   | None -> ty_err ("Error at LetBind"))

  | Lambda(strx,t_opt,e_lambda) -> 
   (match t_opt with
   | Some t -> TFun(t,typecheck (Env.add (strx) (t) (env)) (e_lambda))
   | None -> ty_err ("Error at Lambda"))

  | App(e1,e2) -> 
   (match typecheck (env) (e1) with
   | TFun(t1, t2) -> 
      (if typecheck (env) (e2) = t1
      then t2
      else ty_err ("Error at App"))
   | _ -> ty_err ("Error at App"))

  | ListNil t_opt -> 
   (match t_opt with
   | Some t -> TList t
   | None -> ty_err ("Error at ListNil"))

  | ListCons(e1,e2) -> 
   (match typecheck (env) (e2) with
   |TList t -> 
      (if typecheck (env) (e1) = t 
      then TList t
      else ty_err ("Error at ListCons"))
   | _ -> ty_err ("Error at ListCons"))

  | ListHead e1 -> 
   (match typecheck (env) (e1) with
   | TList t -> t
   | _ -> ty_err ("Error at ListHead"))

  | ListTail e1 -> 
   (match typecheck (env) (e1) with
   | TList t -> TList t
   | _ -> ty_err ("Error at ListTail"))

  | ListIsNil e1 -> 
   (match typecheck (env) (e1) with
   | TList _ -> TInt
   | _ -> ty_err ("Error at ListIsNil"))

  | Fix e1 ->
   (match typecheck (env) (e1) with
   | TFun(t1,t2) -> 
      (if t1=t2
      then t1
      else ty_err ("Error at Fix"))
   | _ -> ty_err ("Error at Fix"))
  with
  | Type_error msg -> ty_err (msg ^ "\nin expression " ^ string_of_expr e)
