open Env
open Ast
open Util
open Prast

(* --------------------------------------------------------------------------
 * EXCEPTIONS
 * -------------------------------------------------------------------------- *)
open Exception

(* --------------------------------------------------------------------------
 * ENVIRONMENT AND CONTEXT
 * -------------------------------------------------------------------------- *)
type ty_from = ((ty_dist option) ty option)
type ty_to   = ((ty_dist option) ty)

type fenv_value = { args_ty: (unit ty) list; ret_ty: ty_to }
and  fenv = fenv_value SMap.t

(* TODO: Support polymorphic functions *)
let fenv = SMap.empty |> SMap.add "Size" ({ args_ty=[ListTy(FloatTy())]
                                          ; ret_ty=IntTy(Some(Dist(FloatDist 0.0)))
                                          })
                      |> SMap.add "Abs" ({ args_ty=[FloatTy()]
                                         ; ret_ty=FloatTy(Some(Dist(FloatDist 0.0)))
                                         })


type venv_value = { ty: ty_to; mut: bool }
and  venv = venv_value SMap.t

type ctxt = { venv             : venv
            ; ret_ty           : ty_to option
            ; expected_ty      : (ty_dist option) ty option
            ; lnum             : lnum
            ; allow_epsilonvar : bool
            ; allow_hatvar     : bool
            }

let update_venv (var: string) (data: venv_value) (ctxt: ctxt) : ctxt =
  let { venv; ret_ty; expected_ty; lnum; allow_epsilonvar; allow_hatvar } = ctxt
  in let venv' = SMap.add var data venv
  in { venv=venv'; ret_ty; expected_ty; lnum; allow_epsilonvar; allow_hatvar }

let update_expected_ty (expected_ty: (ty_dist option) ty option) (ctxt: ctxt) : ctxt =
  let { venv; ret_ty; lnum; allow_epsilonvar; allow_hatvar } = ctxt
  in { venv; ret_ty; expected_ty; lnum; allow_epsilonvar; allow_hatvar }

let update_lnum (lnum: lnum) (ctxt: ctxt) : ctxt =
  let { venv; ret_ty; expected_ty; allow_epsilonvar; allow_hatvar } = ctxt
  in { venv; ret_ty; expected_ty; lnum; allow_epsilonvar; allow_hatvar }

let update_allowed_special_vars allow_epsilonvar allow_hatvar (ctxt: ctxt) : ctxt =
  let { venv; ret_ty; expected_ty; lnum } = ctxt
  in { venv; ret_ty; expected_ty; lnum; allow_epsilonvar; allow_hatvar }

(* --------------------------------------------------------------------------
 * HELPER FUNCTIONS
 * -------------------------------------------------------------------------- *)

(* Type extraction from subtrees *)
let ty_of_dist dist : unit ty =
  match dist with
  | IntDist _           -> IntTy ()
  | EpsilonDist _
  | FloatDist _
  | DVarDist _         -> FloatTy ()
  | HatVarDist{ty}
  | VarDist{ty}
  | UMinusDist{ty}
  | OpDist{ty}
  | TernaryDist{ty}
  | SubDist{ty}         ->
    begin
      match ty with
      | Some(ty) -> ty
      | None -> raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__))
    end
  | TypeCastDist{to_ty} -> to_ty
  | Error               -> Error


let rec hat_var_type (ty: ty_to) : ty_to option =
  match ty with
  | FloatTy(_) -> Some(FloatTy(None))
  | ListTy(inner) ->
    begin match hat_var_type inner with
     | Some(inner') -> Some(ListTy(inner'))
     | None -> None
    end
  | _ -> None


(* --------------------------------------------------------------------------
 * EXPLICIT DISTANCES
 * -------------------------------------------------------------------------- *)

(* TODO: This is almost the same function as in refine.ml *)
let rec dist_of_ty (ty: ty_to) : dist option  =
  match ty with
  | Error                 -> None
  | ListTy(inner)         -> dist_of_ty inner
  | IntTy dist
  | FloatTy dist          ->
    begin
      match dist with
      | Some(Dist(dist')) -> Some(dist')
      | _                 -> None
    end
  | BoolTy                -> None

(* TODO: Unit tests *)
let rec s_dist (dist: dist) (ctxt: ctxt) : dist =
  let { venv; expected_ty; lnum } = ctxt
  in let ensure_expected_ty dist =
       let dist_ty = ty_of_dist dist
       in match expected_ty with
       | None -> dist
       | Some expected_ty ->
         if eq_bty dist_ty expected_ty
         then dist
         else begin match (dist_ty, expected_ty) with
           | (IntTy(_), FloatTy(_)) ->
             TypeCastDist{ to_ty=FloatTy (); dist=dist }
           | (BoolTy, BoolTy) -> dist
           | (ListTy(inner1), ListTy(inner2)) ->
             if eq_bty inner1 inner2
             then dist
             else let rec ensure_lists ty1 ty2 : bool =
                    match (ty1, ty2) with
                    | (ListTy(i1), ListTy(i2)) -> ensure_lists i1 i2
                    | (FloatTy(_), IntTy(_)) -> true
                    | _ -> false
               in if ensure_lists inner1 inner2
               then TypeCastDist{ to_ty=ListTy (update_dist inner2 ()); dist=dist}
               else
                 ( "Expected '?' to be of type '"^(string_of_ty expected_ty)^"' but got '"^
                   (string_of_ty dist_ty)^"'." |> print_error lnum
                 ; Error)
           | _ -> ( "Expected '?' to be of type '"^(string_of_ty expected_ty)^"' but got '"^
                    (string_of_ty dist_ty)^"'." |> print_error lnum
                  ; Error)
         end

  in match dist with
     | EpsilonDist{lnum} -> ensure_expected_ty (EpsilonDist{lnum})
     | IntDist n         -> ensure_expected_ty (IntDist n)
     | FloatDist n       -> ensure_expected_ty (FloatDist n)
     | VarDist{var; ty}  ->
       begin match ty with
         | Some(ty') -> ensure_expected_ty (VarDist{var; lnum; ty})
         | None ->
           let var_ty_opt = SMap.find_opt var venv
           in begin match var_ty_opt with
             | None ->
               ("Undefined variable: '"^var^"' in distance"
                |> print_error lnum; Error)
             | Some({ty;mut}) ->
               ensure_expected_ty (VarDist{var; lnum; ty=Some(update_dist ty ())})
           end
       end

     | HatVarDist{lnum; var; ty} ->
       begin match SMap.find_opt var venv with
         | Some({ty; mut}) ->
           begin
             match hat_var_type ty with
             | Some(ty') -> ensure_expected_ty (HatVarDist{var=var
                                                          ; lnum=lnum
                                                          ; ty=Some(update_dist ty' ())
                                                          })
             | None -> ("Cannot hat "^var^" of type '"^(string_of_ty ty)^"'"
                        |> print_error lnum; Error)
           end
         | None -> ("Undefined variable '"^var^"'" |> print_error lnum; Error)
       end

     | DVarDist(dvar) ->
       (* These should not exist in the AST at this point, since they will be
          introduced first in the refinement phase. *)
       raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__))

     | UMinusDist{lnum; dist} ->
       begin match s_dist dist (ctxt |> update_lnum lnum) with
         | Error -> Error
         | dist' ->
           let ty' = ty_of_dist dist'
           in if is_number ty'
           then UMinusDist{lnum=lnum; dist=dist'; ty=Some(ty') }
           else ("Unary minus operator expected 'int' or 'float' type but got"^
                 (string_of_ty ty') |> print_error lnum; Error)
       end

     | OpDist{lnum; left; right; op} ->
       begin match op with
         | PlusOp | MinusOp | TimesOp | DivideOp
         | EqOp | LtOp | LeOp | GtOp | GeOp ->
           let left' = s_dist left (ctxt |> update_expected_ty None |> update_lnum lnum)
           in let right' = s_dist right (ctxt |> update_expected_ty None |> update_lnum lnum)
           in begin match (left', right') with
             | (Error, _) | (_, Error) -> Error
             | _ ->
               let left_ty = ty_of_dist left'
               in let right_ty = ty_of_dist right'
               in let ty_eq = eq_bty left_ty right_ty
               in let res_ty = match op with
                   | PlusOp | MinusOp | TimesOp | DivideOp ->
                     if ty_eq then right_ty else FloatTy()
                   | _ -> BoolTy
               in if is_number left_ty && is_number right_ty
               then if ty_eq
                 then ensure_expected_ty (OpDist{ lnum=lnum
                                                ; left=left'
                                                ; right=right'
                                                ; op=op
                                                ; ty=Some res_ty })
                 else
                   let left'' = match left_ty with
                     | IntTy(_) -> TypeCastDist{ to_ty=FloatTy ()
                                               ; dist=left' }
                     | _ -> left'
                   in let right'' = match right_ty with
                       | IntTy(_) -> TypeCastDist{ to_ty=FloatTy ()
                                                 ; dist=right' }
                       | _ -> right'
                   in ensure_expected_ty (OpDist{ lnum=lnum
                                                ; left=left''
                                                ; right=right''
                                                ; op=op
                                                ; ty=Some res_ty })
               else ("Operator '"^(pty_op op)^"' expects two arguments of type"^
                     "'int' or 'float' but got '"^(string_of_ty left_ty)^"' and '"^
                     (string_of_ty right_ty)^"' respectively" |> print_error lnum
                    ; Error)
           end

         | ModuloOp ->
           let left' = s_dist left (ctxt |> update_expected_ty (Some (IntTy None)) |> update_lnum lnum)
           in let right' = s_dist right (ctxt |> update_expected_ty (Some (IntTy None)) |> update_lnum lnum)
           in ensure_expected_ty (OpDist{ lnum=lnum
                                        ; left=left'
                                        ; right=right'
                                        ; op=op
                                        ; ty=Some (IntTy ())})

         | AndOp | OrOp | ImpliesOp ->
           let left' = s_dist left (ctxt |> update_expected_ty (Some BoolTy) |> update_lnum lnum)
           in let right' = s_dist left (ctxt |> update_expected_ty (Some BoolTy) |> update_lnum lnum)
           in ensure_expected_ty (OpDist{ lnum=lnum
                                        ; left=left'
                                        ; right=right'
                                        ; op=op
                                        ; ty=Some BoolTy})
       end

     | SubDist{lnum; list; idx} ->
       let list' = s_dist list (ctxt |> update_expected_ty None |> update_lnum lnum)
       in let list_ty = ty_of_dist list'
       in let idx' = s_dist idx (ctxt |> update_expected_ty (Some (IntTy None)) |> update_lnum lnum)
       in let idx_ty = ty_of_dist idx'
       in begin match (list_ty, idx_ty) with
         | (Error,_) | (_, Error) -> Error
         | (ListTy(ty), _) ->
           ensure_expected_ty (SubDist { lnum=lnum
                                       ; list=list'
                                       ; idx=idx'
                                       ; ty=Some(update_dist ty ()) })
         | _ ->
           ("Expected list type but got '"^(string_of_ty list_ty)^"'"
            |> print_error lnum; Error)
       end

     | TernaryDist{cond_dist; then_lnum; then_dist; else_lnum; else_dist} ->
       let cond_dist' = s_dist cond_dist (ctxt |> update_expected_ty (Some BoolTy) |> update_lnum lnum)
       in let cond_ty = ty_of_dist cond_dist'
       in let then_dist' = s_dist then_dist (ctxt |> update_lnum lnum)
       in let then_ty = ty_of_dist then_dist'
       in let else_dist' = s_dist else_dist (ctxt |> update_lnum lnum)
       in let else_ty = ty_of_dist else_dist
       in begin match (cond_ty, then_ty, else_ty) with
            | (Error, _, _) | (_, Error,_) | (_, _,Error) -> Error
            | _ ->
              if eq_bty then_ty else_ty
              then
                (TernaryDist{ cond_dist=cond_dist'
                            ; then_lnum=then_lnum
                            ; then_dist=then_dist'
                            ; else_lnum=else_lnum
                            ; else_dist=else_dist'
                            ; ty=Some else_ty})
              else (* We know that they do not have the same type => expected_ty = none *)
                if is_number else_ty && is_number then_ty
                then let then_dist'' = match then_ty with
                                              | IntTy(_) -> TypeCastDist{ to_ty=FloatTy ()
                                                                        ; dist=then_dist' }
                                              | _ -> then_dist'
                     in let else_dist'' = match else_ty with
                                              | IntTy(_) -> TypeCastDist{ to_ty=FloatTy ()
                                                                        ; dist=else_dist' }
                                              | _ -> else_dist'
                     in (TernaryDist{ cond_dist=cond_dist'
                                    ; then_lnum=then_lnum
                                    ; then_dist=then_dist''
                                    ; else_lnum=else_lnum
                                    ; else_dist=else_dist''
                                    ; ty=Some (FloatTy ())})
                else ("Type mismatch in ternary branches: Got '"^(string_of_ty then_ty)^"' and '"^
                     (string_of_ty else_ty)^"'" |> print_error else_lnum; Error)
          end

     | TypeCastDist{dist; to_ty} ->
       (* We don't allow programmers to write typecasts, so these
       ** shouldn't appear here, right? *)
       raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__))

     | Error -> Error


(* --------------------------------------------------------------------------
 * EXPRESSIONS
 * -------------------------------------------------------------------------- *)
let rec s_exp (exp : ty_from exp) (ctxt: ctxt) : ty_to exp =
  let { venv; ret_ty; expected_ty; lnum; allow_epsilonvar; allow_hatvar } = ctxt
  in match exp with
  (* Literals *)
  | IntExp(n)        -> IntExp n
  | FloatExp(n)      -> FloatExp n
  | EpsilonExp{lnum} -> EpsilonExp{ lnum=lnum }
  | BoolExp(b)       -> BoolExp b

  | EpsilonVarExp{lnum} ->
    if allow_epsilonvar
    then EpsilonVarExp{ lnum }
    else ("The privacy leakage variable 'v_epsilon' may only be used in invariants"
         |> print_error lnum; Error)

  (* Variables *)
  | VarExp{ var }   ->
    begin match SMap.find_opt var venv with
      | Some({ty; mut}) ->
        VarExp{ var=var; lnum; ty=update_dist ty None }
      | None -> ("Undefined variable '"^var^"'" |> print_error lnum; Error)
    end

  | HatVarExp{var; lnum; ty} ->
    if allow_hatvar
    then match SMap.find_opt var venv with
          | Some({ty; mut}) ->
            begin
              match hat_var_type ty with
              | Some(ty') -> HatVarExp{var=var; lnum=lnum; ty=ty'}
              | None -> ("Cannot use distance operator ^ on variable '"^var^"' of type '"^(string_of_ty ty)^"'"
                        |> print_error lnum; Error)
            end
          | None -> ("Undefined variable '"^var^"'" |> print_error lnum; Error)
    else ("The distance variable '^"^var^"' is only allowed to be referenced within annotations" |> print_error lnum; Error)

  (* Operations *)
  | UMinusExp{lnum; exp} ->
    begin
      match s_exp exp (ctxt |> update_lnum lnum) with
      | Error -> Error
      | exp' ->
        let ty' = ty_of_exp exp' None
        in if is_number ty'
        then UMinusExp{lnum=lnum; exp=exp'; ty=ty'}
        else ("Cannot unary minus '"^(pty_exp exp)^"' of type '"^(string_of_ty ty')^"'"
              |> print_error lnum; Error)
    end

  | OpExp{lnum; left; right; op} ->
    begin
      match (s_exp left ctxt, s_exp right (ctxt |> update_lnum lnum)) with
      | (Error, _) | (_, Error) -> Error
      | (left', right') ->
        let left_ty = ty_of_exp left' None
        in let right_ty = ty_of_exp right' None
        in let res_opt =
             match op with
             | PlusOp | MinusOp | TimesOp | DivideOp
             | EqOp | LtOp | LeOp | GtOp | GeOp ->
               if is_number left_ty
               then if is_number right_ty
                 then if eq_bty left_ty right_ty
                   then match op with
                     | PlusOp | MinusOp | TimesOp | DivideOp ->
                       Some(left_ty, left_ty)
                     | _ ->
                       Some(left_ty, BoolTy)
                   else match op with
                     | PlusOp | MinusOp | TimesOp | DivideOp ->
                       Some(FloatTy None, FloatTy None)
                     | _ ->
                       Some(FloatTy None, BoolTy)
                 else ("Expected '"^(pty_exp right)^"' to be of type 'int' or 'float' but got '"^
                       (string_of_ty right_ty)^"'" |> print_error lnum; None)
               else ("Expected '"^(pty_exp left)^"' to be of type 'int' or 'float' but got '"^
                     (string_of_ty left_ty)^"'" |> print_error lnum; None)

             | ModuloOp ->
               begin
                 match (left_ty, right_ty) with
                 | (IntTy _, IntTy _) -> Some(IntTy None, IntTy None)
                 | _ -> ("Cannot apply modulo operator on '"^(pty_exp left)^
                         "' of type '"^(string_of_ty left_ty)^
                         "' and '"^(pty_exp right)^"' of type '"^(string_of_ty right_ty)^"'"
                         |> print_error lnum; None)
               end

             | AndOp | OrOp | ImpliesOp ->
               begin
                 match (left_ty, right_ty) with
                 | (BoolTy, BoolTy) -> Some(BoolTy, BoolTy)
                 | _ -> ("Cannot apply boolean operator on '"^(pty_exp left)^
                         "' of type '"^(string_of_ty left_ty)^
                         "' and '"^(pty_exp right)^"' of type '"^(string_of_ty right_ty)^"'"
                         |> print_error lnum; None)
               end

        in let cast_if_needed exp exp_ty cast_to_ty =
             match (exp_ty, cast_to_ty) with
             | (IntTy(_), FloatTy(_)) -> TypeCastExp{ lnum=lnum
                                                    ; to_ty=FloatTy ()
                                                    ; exp=exp }
             | _ -> exp
        in begin match res_opt with
          | Some((cast_to_ty, res_ty)) -> OpExp{ lnum=lnum
                                            ; left=cast_if_needed left' left_ty cast_to_ty
                                            ; right=cast_if_needed right' right_ty cast_to_ty
                                            ; op=op
                                            ; ty=res_ty }
          | _ -> Error
        end
    end

  (* Boolean expressions *)
  | NotExp{lnum; exp} ->
    let exp' = s_exp exp (ctxt |> update_lnum lnum)
    in let ty' = ty_of_exp exp' None
    in begin
      match ty' with
      | BoolTy -> NotExp{lnum=lnum; exp=exp'}
      | Error -> Error
      | _ -> ("Expected '"^(pty_exp exp)^"' to be of type 'bool' but it has type '"^
              (string_of_ty ty')^"'" |> print_error lnum
             ; Error)
    end

  | TernaryExp{cond_exp; then_lnum; then_exp; else_lnum; else_exp} ->
    begin
      let ctxt' = ctxt |> update_lnum lnum
      in match (s_exp cond_exp ctxt', s_exp then_exp ctxt', s_exp else_exp ctxt') with
      | (Error, _, _) | (_, Error, _) | (_, _, Error) -> Error
      | (cond', then', else') ->
        let cond_ty' = ty_of_exp cond' None
        in let then_ty' = ty_of_exp then' None
        in let else_ty' = ty_of_exp else' None
        in if is_bool cond_ty'
        then if eq_bty then_ty' else_ty'
          then TernaryExp{ cond_exp=cond'
                         ; then_lnum=then_lnum; then_exp=then'
                         ; else_lnum=else_lnum; else_exp=else'
                         ; ty=then_ty' }
          else (("Type of '"^(pty_exp then_exp)^"' and '"^(pty_exp else_exp)^
                 "' do not match for ternary"
                 |> print_error then_lnum); Error)
        else (("Expected conditional '"^(pty_exp cond_exp)^
               "' in ternary of type 'bool' but got '"^(string_of_ty cond_ty')^"'"
               |> print_error then_lnum); Error)
    end

  (* List expressions *)
  | NilExp{lnum} ->
    begin
      match expected_ty with
      | Some(ListTy inner) -> NilExp{lnum=lnum; ty=ListTy(inner)}
      | Some(ty) -> ("Expected '"^(string_of_ty ty)^"' but found '"^(string_of_ty (ListTy Error))^"'"
                     |> print_error lnum; Error)
      | None -> "Cannot infer type of empty list" |> print_error lnum; Error
    end

  | ConcatExp{lnum; elem; list}  ->
    begin
      match s_exp elem ctxt with
      | Error -> Error
      | elem' ->
        let elem_ty' = ty_of_exp elem' None
        in let ctxt' = ctxt
                       |> update_expected_ty (Some(ListTy elem_ty'))
                       |> update_lnum lnum
        in match s_exp list ctxt' with
            | Error -> Error
            | list' ->
              begin
                match ty_of_exp list' None with
                | ListTy(list_inner_ty') ->
                  if eq_bty list_inner_ty' elem_ty'
                  then ConcatExp{lnum=lnum; elem=elem'; list=list'; ty=ListTy(list_inner_ty')}
                  else ( "Cannot concatenate '"^(pty_exp elem)^
                         "' of type '"^(string_of_ty elem_ty')^
                         "' onto '"^(pty_exp list)^
                         "' of type 'list("^(string_of_ty list_inner_ty')^")'"
                         |> print_error lnum
                       ; Error)

                | _ -> ( "Cannot concatenate onto expression '"^(pty_exp list)^"'of non-list type"
                         |> print_error lnum
                       ; Error)
              end
    end

  | SubExp{lnum; list; idx}   ->
    let ctxt' = ctxt |> update_lnum lnum
    in begin match (s_exp list ctxt', s_exp idx ctxt') with
      | (Error, _) | (_, Error) -> Error
      | (list', idx') ->
        let idx_ty' = ty_of_exp idx' None
        in let list_ty' = ty_of_exp list' None
        in begin
          match idx_ty' with
          | IntTy(_) ->
            begin
              match list_ty' with
              | ListTy(list_inner_ty') ->
                SubExp{lnum=lnum; list=list'; idx=idx'; ty=list_inner_ty'}
              | _ -> ("Cannot subcript '"^(pty_exp list)^"' of type '"^(string_of_ty list_ty')^"'"
                      |> print_error lnum; Error)
            end
          | Error -> Error
          | _ -> "Index '"^(pty_exp idx)^"' into list must be of type 'int', but found '"^
                 (string_of_ty idx_ty')^"'" |> print_error lnum; Error
        end
    end

  (* Functions *)
  | CallExp{lnum; func; args} ->
    let args_init : (ty_to exp list * ty_to list) option = Some(([], []))
    in let args_types = List.fold_left
           (fun acc arg -> match (s_exp arg (ctxt |> update_lnum lnum), acc) with
              | (Error, _) | (_, None) -> None
              | (arg', Some(args,tys)) ->
                let ty' = ty_of_exp arg' None
                in Some((arg'::args, ty'::tys)))
           args_init
           args

    in begin match func with
      (* TODO: One could instead make "Lap obligations"? In refinement! *)
      | "Lap"  -> raise (NotImplemented "Use of lap deep inside an expressions is not supported")
      | _ -> (match (SMap.find_opt func fenv, args_types) with
          | (Some({ args_ty; ret_ty }), Some(( args', args_ty' ))) ->
            let matches = List.fold_left2
                (fun (acc: bool) expected inferred ->
                   if eq_bty expected inferred
                   then acc && true
                   else ("Argument type mismatch. Expected '"^(string_of_ty expected)^
                         "' but found '"^(string_of_ty inferred)^"'" |> print_error lnum;
                         false)
                )
                true
                args_ty
                args_ty'
            in if matches
            then CallExp{lnum=lnum; func=func; args=args'; ty=ret_ty}
            else Error

          | (None, _) -> ("Unknown function '"^func^"'" |> print_error lnum
                         ; Error)
          | (_, None) -> Error)
    end

  (* Type casting*)
  | TypeCastExp{ to_ty; exp; lnum } ->
    raise (NotImplemented (__FILE__ ^" : "^ string_of_int __LINE__))

  (* Error handling - propagate error upwards *)
  | Error -> Error

(* --------------------------------------------------------------------------
 * ANNOTATION EXPRESSIONS (preconditions, postconditions and loop invariants)
 * -------------------------------------------------------------------------- *)

let rec s_aexp (aexp : ty_from aexp) (ctxt: ctxt) : ty_to aexp option =
  match aexp with
  | Quantifier(_, vars, None, _) ->
    ("Untyped quantifiers '"^(String.concat ", " vars)^"' in annotation" |> print_error None
    ; None)
  | Quantifier(aquant, vars, Some(ty), aexp') ->
    let ctxt' = List.fold_left
        (fun acc_ctxt var -> update_venv var { ty=ty; mut=false } acc_ctxt)
        ctxt
        vars
    in (match s_aexp aexp' ctxt' with
        | None        -> None
        | Some(aexp') -> Some(Quantifier(aquant, vars, ty, aexp')))

  | Prop(exp) ->
    begin
      match s_exp exp ctxt with
        | Error -> None
        | exp'  ->
        let prop_ty = ty_of_exp exp' None
        in if is_bool prop_ty
           then Some(Prop(exp'))
           else ("Proposition '"^(pty_exp exp')^"' in annotation has type '"^
                 (string_of_ty prop_ty)^"', but only propositions of type 'bool' is allowed"
                 |> print_error None; None)
    end

let rec s_anno (ctxt: ctxt) (is_legal_anno : avariant -> bool) (anno: ty_from annotation) : ty_to annotation =
  match anno with
  | Error -> Error
  | Annotation{lnum; av; aexp} ->
    if is_legal_anno av
    then match (av, aexp) with
      | (Termination, Prop(exp)) ->
        let exp' = s_exp exp ctxt
        in let exp_ty = ty_of_exp exp' None
        in if is_number exp_ty
        then Annotation{lnum; av; aexp=Prop(exp')}
        else ("The termination fucntion '"^(pty_exp exp')^"' in annotation has type '"^
               (string_of_ty exp_ty)^"', but has to be of type 'int' or 'float'"
               |> print_error lnum
              ; Error)
      | _ ->
        let ctxt' = match av with
          | Invariant -> ctxt |> update_allowed_special_vars true true
          | _ -> ctxt |> update_allowed_special_vars false true
        in begin
          match s_aexp aexp (ctxt' |> update_lnum lnum) with
          | Some(aexp') -> Annotation{lnum; av; aexp=aexp'}
          | None -> Error
        end
    else ("Illegal annotation: '"^(pty_anno anno)^"'" |> print_error lnum; Error)

and s_prog_annos (annos: ty_from annotation list) (ctxt: ctxt) : ty_to annotation list =
  let is_legal_anno av = match av with
    | Precondition | Postcondition -> true
    | _ -> false
  in let annos' = List.map (s_anno ctxt is_legal_anno) annos
  in let error : ty_to annotation = Error
  in if List.mem error annos'
     then [Error]
     else annos'

and s_while_annos (annos: ty_from annotation list) (ctxt: ctxt) : ty_to annotation list =
  let is_legal_anno av = match av with
    | Invariant | Termination -> true
    | _ -> false
  in let annos' = List.map (s_anno ctxt is_legal_anno) annos
  in let error : ty_to annotation = Error
  in if List.mem error annos'
     then [Error]
     else annos'

(* --------------------------------------------------------------------------
 * STATEMENTS
 * -------------------------------------------------------------------------- *)

let rec s_stmts (stmts : ty_from stmt list) (ctxt: ctxt) : ty_to stmt list * ctxt =
  let (stmts_rev, ctxt') = stmts |> List.fold_left
                             (fun ((cs, ctxt'): ty_to stmt list * ctxt) (c: ty_from stmt) ->
                                let (c', ctxt'') = s_stmt c ctxt'
                                in match (cs, c') with
                                | ([Error], _) | (_, Error) -> ([Error], ctxt'')
                                | _                         -> (c'::cs, ctxt''))
                             ([], ctxt)
  in (List.rev stmts_rev, ctxt')

(* TODO: If the type checking fails, we should send the old context back, right? *)
and s_stmt (stmt : ty_from stmt) (ctxt: ctxt) : ty_to stmt * ctxt =
  let { venv; ret_ty; expected_ty; allow_epsilonvar; allow_hatvar } = ctxt
  in match stmt with
  (* DONE: SKIP *)
  | SkipStmt{lnum} -> (SkipStmt{lnum=lnum}, ctxt)

  (* DONE: ASSIGN *)
  | AssignStmt{ lnum; var; exp } ->
    begin
      match SMap.find_opt var venv with
      | Some({ty; mut}) ->
        if mut
        then let exp' = s_exp exp (ctxt |> update_expected_ty (Some ty) |> update_lnum lnum)
          in let ty' = ty_of_exp exp' None
          in if eq_bty ty ty'
          then (AssignStmt{ lnum=lnum; var=var; exp=exp' }, ctxt)
          else ("Expression '"^(pty_exp exp)^"' of type '"^(string_of_ty ty')^
                "' assigned to variable '"^var^"' of type '"^(string_of_ty ty)^"'" |> print_error lnum
               ; (Error, ctxt))
        else ("Cannot assign to immutable variable '"^var^"'" |> print_error lnum
             ; (Error, ctxt))
      | None -> ("Undefined variable: "^var |> print_error lnum
                ; (Error, ctxt))
    end

  (* DONE: DECLARATION | TODO: test *)
  | DeclStmt{ lnum; ty; var; exp; mut } ->
    begin
      match SMap.find_opt var venv with
      | None    ->
        let exp' : ty_to exp = match exp with
          | CallExp{ lnum=lnum2; func="Lap"; args} ->
            (match args with
             | [arg] ->
               (match s_exp arg (ctxt |> update_lnum lnum) with
                | Error -> Error
                | arg' ->
                  let ty' = ty_of_exp arg' None
                  in if is_number ty'
                  then CallExp{ lnum=lnum2
                               ; func="Lap"
                               ; args=[arg']
                               ; ty=FloatTy(None)
                               }
                  else ( "Argument '"^(pty_exp arg')^"' has type '"^(string_of_ty ty')
                         ^"' but expected 'int' or 'float'" |> print_error lnum
                       ; Error )
               )
             | _ -> ( "Expected one argument for Lap function, received "
                      ^(string_of_int (List.length args)) |> print_error lnum
                    ; Error))
          | _ ->  s_exp exp (ctxt |> update_expected_ty ty)

        in let ty' = match ty with
            | None -> ty_of_exp exp' None
            | Some(ty) ->
              if eq_bty ty (ty_of_exp exp' None)
              then ty
              else ("Expression '"^(pty_exp exp)^"' has type '"^(string_of_ty (ty_of_exp exp' None))^
                    "' while '"^var^"' was supposed to be of type '"^(string_of_ty ty)^"'"
                    |> print_error lnum
                   ; Error)
        in begin match ty' with
            | Error -> (Error, ctxt)
            | _ ->
              let ctxt' = ctxt |> update_venv var { ty=ty'; mut=mut } |> update_lnum lnum
              in match dist_of_ty ty' with
                 | None -> (* No distance present, aka nothing to check *)
                  (DeclStmt{ lnum=lnum; ty=ty'; var=var; exp=exp'; mut=mut}, ctxt')
                 | Some(dist) ->
                   let dist' = s_dist dist (ctxt' |> update_expected_ty (Some (FloatTy None)) |> update_lnum lnum)
                   in begin match dist' with
                     | Error -> (Error, ctxt')
                     | _ -> (DeclStmt{ lnum=lnum
                                         ; ty=update_dist ty' (Some (Dist dist'))
                                         ; var=var
                                         ; exp=exp'
                                         ; mut=mut}
                                , ctxt')
                   end
        end

      | Some({ ty=ty'; mut }) ->
        let basic_error = "Variable '"^var^"' is already defined"
        in let extra_error = if mut then ". Did you mean to assign to it?" else ""
        in basic_error^extra_error |> print_error lnum; (Error, ctxt)
    end

  (* DONE: RETURN *)
  | ReturnStmt{ lnum; exp } ->
    let exp' = s_exp exp (ctxt |> update_lnum lnum)
    in let ty' = ty_of_exp exp' None
    in let return_type = match ret_ty with
        | None -> ty'
        | Some(ty) ->
          if eq_bty ty ty'
          then ty
          else ("Expected return type '"^(string_of_ty ty)^"' but type of '"^
                (pty_stmt stmt init_ctxt)^"' is '"^(string_of_ty ty')^"'" |> print_error lnum
               ; Error)
    in let ctxt' = {venv; ret_ty=Some(return_type); expected_ty; lnum; allow_epsilonvar; allow_hatvar }
    in begin
      match return_type with
      | Error -> (Error, ctxt)
      | _ -> (ReturnStmt{ lnum=lnum; exp=exp' }, ctxt')
    end

  (* DONE: IF THEN ELSE *)
  | IfStmt{ cond_lnum; cond_exp; then_lnum; then_body; then_dist_venv; else_lnum; else_body; else_dist_venv } ->
    let cond_exp' = s_exp cond_exp (ctxt |> update_lnum cond_lnum)
    in let cond_ty' = ty_of_exp cond_exp' None
    in (match cond_ty' with
        | BoolTy ->
          let    (then_body', ctxt') = s_stmts then_body ctxt
          in let (else_body', ctxt'') = s_stmts else_body ctxt'
          in (IfStmt{ cond_lnum
                    ; cond_exp=cond_exp'
                    ; then_lnum
                    ; then_body=then_body'
                    ; then_dist_venv
                    ; else_lnum
                    ; else_body=else_body'
                    ; else_dist_venv
                    }
             , ctxt'')
        | _ -> ("Expected conditional of type 'bool' while expression '"^
                (pty_exp cond_exp)^"' has type '"^(string_of_ty cond_ty')^"'"
                |> print_error cond_lnum
               ; (Error, ctxt)))

  (* DONE: WHILE *)
  | WhileStmt{ lnum; cond_exp; annos; body; body_dist_venv } ->
    let cond' = s_exp cond_exp (ctxt |> update_lnum lnum)
    in let cond_ty' = ty_of_exp cond' None
    in let annos' = s_while_annos annos ctxt
    in (match cond_ty' with
        | BoolTy ->
          let (body', ctxt') = s_stmts body ctxt
          in (WhileStmt{ lnum; cond_exp=cond'; annos=annos'; body=body'; body_dist_venv }, ctxt')
        | _ -> ("Expected conditional of type 'bool' while expression '"^
                (pty_exp cond_exp)^"' has type '"^(string_of_ty cond_ty')^"'" |> print_error lnum
               ; (Error, ctxt)))

  (* DONE: ERROR *)
  | Error -> (Error, ctxt)

(* --------------------------------------------------------------------------
 * PROGRAMS
 * -------------------------------------------------------------------------- *)
let rec s_prog_arg (arg: ty_from prog_arg) (ctxt: ctxt) : ty_to prog_arg * ctxt =
  let { venv; lnum } = ctxt
  in match arg with
  | Error                -> (Error, ctxt)
  | Arg { var; ty; mut } ->
    (match SMap.mem var venv with
      | false -> (match ty with
          | Some(ty') ->
            let dist_opt = dist_of_ty ty'
            in let ctxt' = (update_venv var { ty=ty'; mut=mut } ctxt)
            in begin match dist_opt with
                     | None ->
                      (Arg{ var=var; ty=ty'; mut=mut }, ctxt')
                     | Some(dist) ->
                       (* TODO: Do we have to typecast Integers? *)
                       let dist' = s_dist dist (ctxt |> update_expected_ty (Some (FloatTy None)))
                       in begin match dist' with
                               | Error -> (Error, ctxt)
                               | _ -> (Arg{ var; ty=update_dist ty' (Some (Dist dist')); mut }, ctxt')
                       end
            end
          | None -> "Argument '"^var^"' must have a type." |> print_error lnum;
            (Error, ctxt))
      | _     -> "Variable '"^var^"' is already bound" |> print_error lnum;
        (Error, ctxt))

and s_prog_args (args: ty_from prog_arg list) (ctxt: ctxt) : ty_to prog_arg list * ctxt =
  List.fold_right
    (fun (arg: ty_from prog_arg) ((args', ctxt'): ty_to prog_arg list * ctxt) ->
       let (arg', ctxt'') = s_prog_arg arg ctxt'
       in match (args', arg') with
       | ([Error], _) | (_, Error) -> ([Error], ctxt'')
       | _                         -> (arg'::args', ctxt'')
    )
    args
    ([], ctxt)

let s_prog (prog : ty_from prog) : ty_to prog =
  match prog with
  | Error -> Error
  | Program { lnum; annos; stmts; stmts_dist_venv; name; args; ret_ty } ->
    let ctxt: ctxt = { venv = SMap.empty
                     ; ret_ty=ret_ty
                     ; expected_ty=None
                     ; lnum=lnum
                     ; allow_epsilonvar=false
                     ; allow_hatvar=false
                     }
    in let (args', ctxt') = s_prog_args args (ctxt |> update_lnum lnum)
    in let annos' = s_prog_annos annos ctxt'
    in let (stmts', ctxt'') = s_stmts stmts ctxt'
    in let { ret_ty } = ctxt''
    in match (annos', stmts, ret_ty) with
    | ([Error], _, _) | (_, [Error], _) -> Error
    | (_,_,None)                        ->
      "Program return type unit and is trivially private" |> print_error lnum;
      Error
    | (_,_,Some(ret_ty'))               -> Program { lnum
                                                   ; annos=annos'
                                                   ; stmts=stmts'
                                                   ; stmts_dist_venv
                                                   ; name
                                                   ; args=args'
                                                   ; ret_ty=ret_ty'
                                                   }
