open Ast

(* --------------------------------------------------------------------------
 * TYPES
 * -------------------------------------------------------------------------- *)

(* Pretty printing *)
let rec string_of_ty ty =
  match ty with
  | IntTy(_)      -> "int"
  | FloatTy(_)    -> "float"
  | BoolTy        -> "bool"
  | ListTy(inner) -> "list("^(string_of_ty inner)^")"
  | _ -> "_"

let string_of_ty_opt ty_opt =
  match ty_opt with
  | None -> "_"
  | Some(ty) -> string_of_ty ty

(* Predicates and comparisons *)
let rec eq_bty ty1 ty2 : bool =
  match (ty1, ty2) with
  | (IntTy(_), IntTy(_))
  | (FloatTy(_), FloatTy(_))
  | (BoolTy, BoolTy)         -> true
  | (ListTy(i1), ListTy(i2)) -> eq_bty i1 i2
  | _ -> false

let is_bool n = match n with
  | BoolTy -> true
  | _ -> false

let is_number n = match n with
  | IntTy(_) | FloatTy(_) -> true
  | _ -> false

(* Ty manipulation *)
let update_dist (ty: 'a ty) (b: 'b) : 'b ty =
  let rec construct_ty ty : 'b ty =
    match ty with
    | IntTy _       -> IntTy b
    | FloatTy _     -> FloatTy b
    | BoolTy        -> BoolTy
    | ListTy(inner) -> ListTy(construct_ty inner)
    | _             -> Error
  in construct_ty ty

let update_base (ty: 'a ty) (base: 'a ty) : 'a ty =
  let rec construct_ty ty : 'a ty =
    match ty with
    | IntTy _       -> base
    | FloatTy _     -> base
    | BoolTy        -> base
    | ListTy(inner) -> ListTy(construct_ty inner)
    | _             -> Error
  in construct_ty ty

(* --------------------------------------------------------------------------
 * Expressions
 * -------------------------------------------------------------------------- *)
let ty_of_exp (exp: 'd ty exp) (default : 'd) : 'd ty =
  match exp with
  | NotExp(_)
  | BoolExp(_)         -> BoolTy
  | IntExp(_)          -> IntTy default
  | EpsilonExp(_)
  | EpsilonVarExp(_)
  | FloatExp(_)        -> FloatTy default
  | HatVarExp{ty}
  | VarExp{ty}
  | UMinusExp{ty}
  | OpExp{ty}
  | TernaryExp{ty}
  | NilExp{ty}
  | ConcatExp{ty}
  | SubExp{ty}
  | CallExp{ty}        -> ty
  | TypeCastExp{to_ty} -> update_dist to_ty default
  | Error              -> Error

(* --------------------------------------------------------------------------
 * Expressions
 * -------------------------------------------------------------------------- *)


