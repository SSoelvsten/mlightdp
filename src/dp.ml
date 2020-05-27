open Env
open Ast
open Util

(* --------------------------------------------------------------------------
 * EXCEPTIONS
 * -------------------------------------------------------------------------- *)
open Exception

(* --------------------------------------------------------------------------
 * ENVIRONMENT AND CONTEXT
 * -------------------------------------------------------------------------- *)
type ty_from = Refine.ty_to

type ctxt = { venv: dist SMap.t
            ; obligations: (Tast.exp * string) list
            ; expected_dist: dist option
            }

let update_venv (var: string) (d: dist) (ctxt: ctxt) : ctxt =
  let { venv; obligations; expected_dist } = ctxt
  in let venv' = SMap.add var d venv
  in { venv=venv'; obligations; expected_dist }

let merge_with_dist_venv (dist_venv: dist_venv) ctxt : ctxt =
  let { venv; obligations; expected_dist } = ctxt
  in let merge_func key old_opt new_opt =
       match (old_opt, new_opt) with
       | (Some(_), Some(_)) ->
         raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__))
       | (_, None) -> old_opt
       | (None, _) -> new_opt
  in let venv' = SMap.merge merge_func venv dist_venv
  in { venv=venv'; obligations; expected_dist }

let add_obligations (o: (Tast.exp * string) list) ctxt : ctxt =
  let { venv; obligations; expected_dist } = ctxt
  in { venv=venv
     ; obligations=obligations @ o
     ; expected_dist=expected_dist}

let add_obligation (o: Tast.exp * string) ctxt : ctxt =
  let { venv; obligations; expected_dist } = ctxt
  in { venv=venv
     ; obligations=o::obligations
     ; expected_dist=expected_dist}

let union_obligations ctxt1 ctxt2 : ctxt =
  add_obligations (ctxt2.obligations) ctxt1

let set_expected_dist dist ctxt : ctxt =
  let { venv; obligations; expected_dist } = ctxt
  in { venv=venv
     ; obligations=obligations
     ; expected_dist=Some(dist)}

(* --------------------------------------------------------------------------
 * HELPER FUNCTIONS
 * -------------------------------------------------------------------------- *)

(* Derivation of generated variable names *)
let resolve_unique_name (name: string) (ctxt: ctxt) : string =
  let { venv } = ctxt
  in let rec recursive_resolve (suffix: int): string =
       let name' = name ^ (string_of_int suffix)
       in if SMap.mem name' venv then recursive_resolve (suffix+1) else name'
  in recursive_resolve 0

let resolve_hat_name (name: string) (ctxt: ctxt) : string =
  resolve_unique_name (name^"_hat") ctxt

let resolve_dvar_name (name: string) (ctxt: ctxt) : string =
  resolve_unique_name (name^"_dvar") ctxt

(* Converters *)
let tastop_of_op (op: oper) : Tast.oper =
    match op with
    | PlusOp -> Tast.PlusOp
    | MinusOp -> Tast.MinusOp
    | TimesOp -> Tast.TimesOp
    | DivideOp -> Tast.DivideOp
    | ModuloOp -> Tast.ModuloOp
    | EqOp -> Tast.EqOp
    | LtOp -> Tast.LtOp
    | LeOp -> Tast.LeOp
    | GtOp -> Tast.GtOp
    | GeOp -> Tast.GeOp
    | AndOp -> Tast.AndOp
    | OrOp -> Tast.OrOp
    | ImpliesOp -> Tast.ImpliesOp

let rec tastty_of_astty (ty: 'a ty) : Tast.ty =
  match ty with
  | IntTy   _ -> Tast.IntTy
  | FloatTy _ -> Tast.FloatTy
  | BoolTy    -> Tast.BoolTy
  | ListTy i  -> Tast.ListTy(tastty_of_astty i)
  | Error     -> raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__))

let rec tastexp_of_dist (dist: dist) (ctxt: ctxt) : Tast.exp =
  match dist with
  | EpsilonDist{lnum}  -> Tast.EpsilonExp
  | IntDist(n)         -> Tast.IntExp(n)
  | FloatDist(n)       -> Tast.FloatExp(n)
  | VarDist{ var; ty } -> Tast.VarExp(var)
  | HatVarDist{ var }  -> Tast.VarExp(resolve_hat_name var ctxt)
  | DVarDist(v)        -> Tast.VarExp(resolve_dvar_name v ctxt)
  | UMinusDist{ lnum; dist }        ->
    Tast.UMinusExp{ exp=tastexp_of_dist dist ctxt }

  | OpDist{ left; right; op }       ->
    Tast.OpExp{ left=tastexp_of_dist left ctxt
              ; right=tastexp_of_dist right ctxt
              ; op=tastop_of_op op
              }
  | TernaryDist{ cond_dist; then_dist; else_dist } ->
    Tast.TernaryExp{ cond_exp=tastexp_of_dist cond_dist ctxt
                   ; then_exp = tastexp_of_dist then_dist ctxt
                   ; else_exp = tastexp_of_dist else_dist ctxt
                   }
  | SubDist{ lnum; list; idx } ->
    Tast.SubExp { list= tastexp_of_dist list ctxt
                ; idx= tastexp_of_dist idx ctxt }
  | TypeCastDist{ to_ty; dist } ->
    Tast.TypeCastExp{ exp=tastexp_of_dist dist ctxt
                    ; to_ty=tastty_of_astty to_ty }
  | Error -> raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__))

let rec dist_of_exp exp : dist =
  match exp with
  | EpsilonExp{lnum}           -> EpsilonDist{lnum=lnum}
  | EpsilonVarExp{lnum}        -> FloatDist 0.0
  | IntExp(n)                  -> FloatDist (float_of_int n)
  | FloatExp(n)                -> FloatDist n
  | VarExp{ var; lnum; ty }    -> VarDist{ var; lnum; ty=None }
  | HatVarExp{ var; ty; lnum } -> HatVarDist{ var; ty=None; lnum }
  | OpExp{lnum; left; right; op; ty} ->
    OpDist{ lnum=lnum
          ; left=dist_of_exp left
          ; right=dist_of_exp right
          ; op=op
          ; ty=None
          }
  | TernaryExp{cond_exp; then_lnum; then_exp; else_lnum; else_exp; ty} ->
    TernaryDist{ cond_dist=dist_of_exp cond_exp
               ; then_lnum=then_lnum
               ; then_dist=dist_of_exp then_exp
               ; else_lnum=else_lnum
               ; else_dist=dist_of_exp else_exp
               ; ty=None
               }
  | SubExp{lnum; list; idx; ty} ->
    SubDist{ lnum=lnum
           ; list=dist_of_exp list
           ; idx=dist_of_exp idx
           ; ty=None
           }
  | TypeCastExp{ to_ty; exp } ->
    TypeCastDist{ to_ty; dist=dist_of_exp exp }
  | _ -> Error

(* Obligations *)

 let flush_obligations (ctxt: ctxt) : Tast.stmt list * ctxt =
   let { venv; obligations; expected_dist} = ctxt
   in if List.length obligations == 0
   then ([], ctxt)
   else ((Tast.Comment "Could not prove the obligations below:")
         ::(List.map (fun (exp, rulename) -> Tast.Assert(exp,(Some rulename))) obligations)
        , {venv=venv
          ; obligations=[]
          ; expected_dist=expected_dist})

let mk_cmp_obligations (texp1, ty1) dist1 (texp2, ty2) dist2 op rulename ctxt : (Tast.exp * string) list =
  let cast_if_needed texp ty =
    match ty with
    | IntTy _   -> Tast.TypeCastExp{ to_ty=Tast.FloatTy
                                   ; exp=texp
                                   }
    | FloatTy _ -> texp
    | _ ->
      raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__))
  in let left = Tast.OpExp{ left=texp1; right=texp2; op=op }
  in let right1 = Tast.OpExp{ left=cast_if_needed texp1 ty1
                            ; right=tastexp_of_dist dist1 ctxt
                            ; op=Tast.PlusOp }
  in let right2 = Tast.OpExp{ left=cast_if_needed texp2 ty2
                            ; right=tastexp_of_dist dist2 ctxt
                            ; op=Tast.PlusOp }
  in let right = Tast.OpExp{ left=right1; right=right2; op=op }
  in [ (Tast.OpExp{ left=left
                 ; right=right
                 ; op=Tast.ImpliesOp
                }
       , rulename)
     ; (Tast.OpExp{ left=right
                 ; right=left
                 ; op=Tast.ImpliesOp
                }
       , rulename)
     ]

let mk_eq_obligation d1 d2 rulename ctxt : Tast.exp * string =
  (Tast.OpExp{ left=tastexp_of_dist d1 ctxt
             ; right=tastexp_of_dist d2 ctxt
             ; op=Tast.EqOp }
  , rulename)

let mk_zero_obligation dist rulename ctxt : Tast.exp * string =
  mk_eq_obligation dist (FloatDist 0.0) rulename ctxt

(* --------------------------------------------------------------------------
 * EXPRESSIONS
 * -------------------------------------------------------------------------- *)
let rec t_exp (exp : ty_from exp) (ctxt: ctxt) : (Tast.exp * dist) option * ctxt =
  let { venv; obligations; expected_dist } = ctxt
  in let zero_dist = FloatDist 0.0
  in match exp with
  (* Primitives *)
  | EpsilonExp(_)    -> (Some(Tast.EpsilonExp,    zero_dist), ctxt)
  | EpsilonVarExp(_) -> (Some(Tast.EpsilonVarExp, zero_dist), ctxt)
  | BoolExp(b)       -> (Some(Tast.BoolExp b,     zero_dist), ctxt)
  | IntExp(n)        -> (Some(Tast.IntExp n,      zero_dist), ctxt)
  | FloatExp(n)      -> (Some(Tast.FloatExp n,    zero_dist), ctxt)

  (* Variables *)
  | VarExp{var;ty}   ->
    begin match SMap.find_opt var venv with
      | Some(dist) -> (Some(Tast.VarExp var, dist), ctxt)
      | None -> raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__^" (var: '"^var^"')"))
    end

  | HatVarExp{var;ty;lnum} ->
    (Some(Tast.VarExp(resolve_hat_name var ctxt), zero_dist), ctxt)

  (* Operations *)
  | UMinusExp{exp} ->
    let (exp_o, ctxt') = t_exp exp ctxt
    in begin
      match exp_o with
      | Some(texp, dist) -> (Some(Tast.UMinusExp{exp=texp}, dist), ctxt)
      | _ -> (None, ctxt)
    end

  | OpExp{ left; right; op } ->
    let (left_o, left_ctxt) = t_exp left ctxt
    in let (right_o, right_ctxt) = t_exp right ctxt
    in let ctxt' = union_obligations left_ctxt right_ctxt
    in begin match (left_o, right_o) with
      | (Some(left_texp, left_dist), Some(right_texp, right_dist)) ->
        let texp = Tast.OpExp{ left=left_texp
                             ; right=right_texp
                             ; op=tastop_of_op op
                             }
        in (match op with
            | PlusOp | MinusOp   -> (* T-OPlus *)
              let dist' = OpDist { lnum=None
                                 ; left=left_dist
                                 ; right=right_dist
                                 ; op=op
                                 ; ty=None
                                 }
              in (Some(texp,dist'), ctxt')

            | TimesOp | DivideOp -> (* T-OTimes *)
              (* TODO: More sophisticated sensitivity analysis proposed by Reed
                       and Pierce (2010); Gaboardi (2013). *)
              let left_obligation = mk_zero_obligation left_dist "T-OTimes" ctxt
              in let right_obligation = mk_zero_obligation right_dist "T-OTimes" ctxt
              in (Some(texp, FloatDist 0.0)
                 , ctxt |> add_obligation left_obligation |> add_obligation right_obligation)

            | ModuloOp ->
              (* Modulo operation is not injective, so we cannot do randomness
                 alignment. Hence, we require the distance to be 0.           *)
              let obli1 = mk_zero_obligation left_dist "T-Modulo" ctxt
              in let obli2 = mk_zero_obligation right_dist "T-Modulo" ctxt
              in let ctxt' = ctxt |> add_obligation obli1 |> add_obligation obli2
              in (Some(texp, FloatDist 0.0), ctxt')

            | AndOp | OrOp | ImpliesOp ->
              (Some(texp, left_dist), ctxt')

            | EqOp | LtOp | LeOp | GtOp | GeOp -> (* T-ODot *)
              let left_ty = ty_of_exp left ()
              in let right_ty = ty_of_exp right ()
              in let obligations = mk_cmp_obligations
                     (left_texp, left_ty) left_dist
                     (right_texp, right_ty) right_dist
                     (tastop_of_op op)
                     "T-ODot"
                     ctxt
              in let ctxt'' = add_obligations obligations ctxt'
              in (Some(texp, FloatDist 0.0), ctxt'')
          )
      | _ -> (None, ctxt')
    end

  | NotExp{exp} -> (* T-Neg *)
    let (o, ctxt') = t_exp exp ctxt
    in begin match o with
        | Some(inner_texp, dist) -> (Some(Tast.NotExp{ exp=inner_texp }, dist), ctxt')
        | _ -> (None, ctxt')
    end

  | TernaryExp{ cond_exp; then_lnum; then_exp; else_lnum; else_exp} -> (* T-Select *)
    let (condo, ctxt_2) = t_exp cond_exp ctxt
    in let (then_expo, ctxt_3) = t_exp then_exp ctxt_2
    in let (else_expo, ctxt_4) = t_exp else_exp ctxt_3
    in begin match (condo, then_expo, else_expo) with
        | (Some(cond_texp, cond_dist), Some(then_texp, then_dist), Some(else_texp, else_dist)) ->
          let eq_obligation = mk_eq_obligation then_dist else_dist "T-Select" ctxt_4
          in let texp = Tast.TernaryExp{ cond_exp=cond_texp
                                       ; then_exp = then_texp
                                       ; else_exp = else_texp }
          in (Some(texp, then_dist), add_obligation eq_obligation ctxt_4)
        | _ -> (None, ctxt_4)
    end

  | NilExp{lnum} -> (* T-Nil *)
    begin match expected_dist with
      | None -> ("Cannot infer distance of empty list" |> print_error lnum
                ; (None, ctxt))
      | Some(dist) -> (Some(Tast.NilExp, dist), ctxt)
    end

  | ConcatExp{lnum; elem; list} -> (* T-Cons *)
    let (elem', { venv=venv'; obligations=obligations'}) = t_exp elem ctxt
    in begin match elem' with
        | Some(elem_texp, elem_dist) ->
          let (list', ctxt'') = t_exp list (ctxt |> set_expected_dist elem_dist)
          in (match list' with
              | Some(list_texp, list_elem_dist) ->
                let result = Some(Tast.ConcatExp{elem=elem_texp;list=list_texp}
                                 , list_elem_dist)
                in if elem_dist = list_elem_dist
                  then (result, ctxt'')
                  else let obli = mk_eq_obligation elem_dist list_elem_dist "T-Cons" ctxt''
                      in ( result
                          , (add_obligation obli ctxt''))
              | _ -> (None, ctxt''))
        | _ -> (None, ctxt)
    end

  | SubExp{lnum; list; idx} -> (* T-Index *)
    let (list', ctxt') = t_exp list ctxt
    in let (idx', ctxt'') = t_exp idx ctxt'
    in begin match (list', idx') with
      | (Some(list_texp, list_elem_dist), Some(idx_texp, idx_dist)) ->
        (* TODO: We definitely do NOT cover all cases here... *)
        begin match dist_of_exp idx with
          | Error -> (None, ctxt)
          | idx_as_dist ->
            let result = Some(Tast.SubExp{list=list_texp; idx=idx_texp}
                             , SubDist{ lnum=lnum
                                      ; list=list_elem_dist
                                      ; idx=idx_as_dist
                                      ; ty=None })
            in if idx_dist = zero_dist
            then (result, ctxt'')
            else let obli = mk_zero_obligation idx_dist "T-Index" ctxt''
              in (result, (add_obligation obli ctxt''))
        end
      | _ -> (None, ctxt'')
    end

  | CallExp{func; args} -> (* T-FuncCall *)
    begin match func with
       (* TODO: Other functions than list length? *)
     | _ ->
        let (args', ctxt') = List.fold_right
            (fun arg (acc, acc_ctxt) -> match t_exp arg ctxt with
                            | (None, _) -> (None, acc_ctxt)
                            | (Some(arg_texp, _), ctxt') ->
                              let ctxt_union = union_obligations acc_ctxt ctxt'
                              in (match acc with
                                  | None -> (None, ctxt_union)
                                  | Some(li) -> (Some(arg_texp::li), ctxt_union)) )
            args
            (Some([]), ctxt)
        in begin match args' with
            | Some(args') -> (Some(Tast.CallExp{func=func; args=args'}, zero_dist), ctxt')
            | None -> (None, ctxt)
        end
    end

  | TypeCastExp{to_ty; exp} ->
    let (exp_o, ctxt') = t_exp exp ctxt
    in begin
      match exp_o with
      | Some(texp, dist) ->
        (Some(Tast.TypeCastExp{ to_ty=tastty_of_astty to_ty
                              ; exp=texp }
             , dist)
        , ctxt)

      | _ -> (None, ctxt)
    end

  | Error      -> (None, ctxt)


(* --------------------------------------------------------------------------
 * ANNOTATIONS
 * -------------------------------------------------------------------------- *)
let rec t_anno (anno: 'a annotation) (ctxt: ctxt) : Tast.annotation option =
  match anno with
  | Error                       -> raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__))
  | Annotation {lnum; av; aexp} ->
    let tast_variant = match av with
      | Invariant -> Tast.Invariant
      | Termination -> Tast.Termination
      | Precondition -> Tast.Precondition
      | Postcondition -> Tast.Postcondition
    in match t_aexp aexp ctxt with
    | None        -> None
    | Some(aexp') -> Some(tast_variant, aexp')

and t_annos (annos : ty_from annotation list) (ctxt: ctxt) : Tast.annotation list =
  List.fold_right
    (fun (anno: ty_from annotation) (annos': Tast.annotation list) ->
       match t_anno anno ctxt with
       | None -> annos'
       | Some(anno') -> anno'::annos')
    annos
    []

and t_aexp (aexp: ty_from aexp) (ctxt: ctxt) : Tast.aexp option =
  match aexp with
  | Quantifier(q,vars,ty,aexp) ->
    let q' = match q with
      | Exists -> Tast.Exists
      | Forall -> Tast.Forall
    in let ctxt' = vars |> List.fold_left
                     (fun acc_ctxt var -> acc_ctxt |> update_venv var (FloatDist 0.0))
                     ctxt
    in (match t_aexp aexp ctxt' with
        | Some(aexp') -> Some(Tast.Quantifier(q'
                                             , vars
                                             , tastty_of_astty ty
                                             , aexp'))
        | _           -> None)
  | Prop(exp) -> (match t_exp exp ctxt with
      | (Some(exp',ty'), _) -> Some(Tast.Prop(exp'))
      | _                     -> None)


(* --------------------------------------------------------------------------
 * STATEMENTS
 * -------------------------------------------------------------------------- *)
let rec t_stmts (stmts : ty_from stmt list) (ctxt: ctxt) : Tast.stmt list option * ctxt =
  let (stmts_rev, ctxt') = stmts |> List.fold_left
                             (fun ((cs, ctxt'): Tast.stmt list option * ctxt) (c: ty_from stmt) ->
                                let (c', ctxt'') = t_stmt c ctxt'
                                in match (cs, c') with
                                | (None, _) | (_, None) -> (None, ctxt'')
                                | (Some(cs),Some(c'))   -> (Some((List.rev c') @ cs), ctxt''))
                             (Some([]), ctxt)
  in match stmts_rev with
  | None            -> (None, ctxt')
  | Some(stmts_rev) -> (Some(List.rev stmts_rev), ctxt')


and t_stmt (stmt : ty_from stmt) (ctxt: ctxt) : Tast.stmt list option * ctxt =
  let { venv; obligations } = ctxt
  in match stmt with
  (* DONE: T-Skip    | TODO: test *)
  | SkipStmt(_) ->
    (Some([Tast.SkipStmt]), ctxt)

  (* DONE: T-Laplace | TODO: test *)
  | AssignStmt{lnum; var; exp=CallExp{ func="Lap"; args=[r] }}
  | DeclStmt  {lnum; var; exp=CallExp{ func="Lap"; args=[r] }} ->
    let (r_opt, ctxt') = t_exp r ctxt
    in (match r_opt with
        | Some(r_texp, r_dist) ->
          (* Create is_zero obligation for r_dist and collect all other obligations *)
          let assert_zero = mk_zero_obligation r_dist "T-Laplace" ctxt
          in let (assertions, ctxt'') = flush_obligations (add_obligation assert_zero ctxt')
          (* Create Havoc statement *)
          in let havoc = Tast.HavocStmt{ var=var }
          (* Counter incrementation *)
          in let var_dist = match SMap.find_opt var venv with
              | Some(v) -> tastexp_of_dist v ctxt'
              | None    -> raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__^" (var: '"^var^"')"))
          in let var_abs_dist = Tast.CallExp{ func="Abs"; args=[var_dist] }
          in let incr_value_texp = Tast.OpExp{ left=var_abs_dist
                                             ; right=r_texp
                                             ; op=Tast.DivideOp }
          in let incr_texp = Tast.OpExp{ left=Tast.EpsilonVarExp
                                       ; right=incr_value_texp
                                       ; op=Tast.PlusOp }
          in let incr_stmt = Tast.AssignStmt { var=Tast.EpsilonVar
                                             ; exp=incr_texp }
          (* Combine it all! *)
          in (Some(assertions @ [havoc; incr_stmt]), ctxt'')
        | None -> (None, ctxt))

  (* DONE: T-Asgn      | TODO: test *)
  (* DONE: T-Asgn-Star | TODO: test *)
  | AssignStmt{lnum; var; exp}
  | DeclStmt  {lnum; var; exp} ->
    let var_dist = SMap.find var venv
    in let (tast_exp_option, ctxt') = t_exp exp (ctxt |> set_expected_dist var_dist)
    in (match tast_exp_option with
        | Some(texp, dist) ->
          let assign_star =
                match var_dist with
                | HatVarDist(var') -> true
                | _ -> false
          in let ctxt'' =
               if assign_star
               then ctxt'
               else let assert_eq = mk_eq_obligation dist var_dist "T-Asgn" ctxt
                 in add_obligation assert_eq ctxt'
          in let (assertions, ctxt''') = flush_obligations ctxt''
          in let result = match stmt with
              | AssignStmt(_)  ->
                (* Assignment to variable *)
                Tast.AssignStmt{var=Tast.Var var; exp=texp}
                :: if assign_star
                (* Assignment to hat variable *)
                then [Tast.AssignStmt{ var=Tast.GhostVar (resolve_hat_name var ctxt''')
                                     ; exp=tastexp_of_dist dist ctxt'''
                                     }]
                else []
              | DeclStmt{ ty; mut } ->
                if mut && match ty with
                  | ListTy _ -> assign_star
                  | _ -> false
                then raise (DevMessage "Mutable star-typed lists are currently not supported.")
                else (* Declaration of variable *)
                  Tast.DeclStmt{var=Tast.Var var; ty=tastty_of_astty ty; exp=texp}
                  (* Declaration of accompanying hat variable *)
                  :: if assign_star
                  then [Tast.DeclStmt{ var=Tast.GhostVar (resolve_hat_name var ctxt''')
                                     (* The hat variable may have type 'list(float)' *)
                                     ; ty=tastty_of_astty (update_base ty (FloatTy ()))
                                     (* TODO: Shouldn't we then pack this into a list of the same length? *)
                                     ; exp=tastexp_of_dist dist ctxt'''
                                     }]
                  else []
              | _ -> raise (DevMessage "unreachable")
          in (Some(assertions @ result), ctxt''')
        | None -> (None, ctxt))

  (* DONE: T-Return | TODO: test *)
  | ReturnStmt{ lnum; exp } ->
    let (tast_exp_option, ctxt') = t_exp exp ctxt
    in (match tast_exp_option with
        | Some(texp, dist) ->
          let assert_zero = mk_zero_obligation dist "T-Return" ctxt
          in let (assertions, ctxt'') = flush_obligations (add_obligation assert_zero ctxt')
          in let epsilon_guard = Tast.Assert (Tast.OpExp{ left=Tast.EpsilonVarExp
                                                        ; right=Tast.EpsilonExp
                                                        ; op=Tast.LeOp }
                                             , Some "T-Return")
          in (Some(assertions @ [epsilon_guard; Tast.ReturnStmt{ exp=texp }]), ctxt'')
        | None -> (None, ctxt))

  (* DONE: T-If | TODO: test *)
  | IfStmt{ cond_exp; then_body; then_dist_venv; else_body; else_dist_venv } ->
    let (cond_exp_opt, ctxt') = t_exp cond_exp ctxt
    in (match cond_exp_opt with
        | Some(cond_exp', _) ->
          let (assertions, ctxt'') = flush_obligations ctxt'
          in let (then_body_opt, _) = t_stmts then_body (ctxt'' |> merge_with_dist_venv then_dist_venv)
          in let (else_body_opt, _) = t_stmts else_body (ctxt'' |> merge_with_dist_venv else_dist_venv)
          in (match (then_body_opt, else_body_opt) with
              | (Some(then_body'), Some(else_body')) ->
                (Some(assertions @ [Tast.IfStmt{ cond_exp=cond_exp'
                                               ; then_body=then_body'
                                               ; else_body=else_body' }])
                , ctxt'')
              | _ -> (None, ctxt))
        | _ -> (None, ctxt))

  (* DONE: T-While | TODO: test *)
  | WhileStmt{ cond_exp; annos; body; body_dist_venv } ->
    let (cond_exp_opt, ctxt') = t_exp cond_exp ctxt
    in (match cond_exp_opt with
        | Some(cond_exp', _) ->
          let (assertions, ctxt'') = flush_obligations ctxt'
          in let (body_opt, _) = t_stmts body (ctxt'' |> merge_with_dist_venv body_dist_venv)
          in let annos' = t_annos annos ctxt''
          in (match body_opt with
              | Some(body') ->
                (Some(assertions @ [Tast.WhileStmt{ cond_exp=cond_exp'
                                                  ; annos=annos'
                                                  ; body=body' }])
                , ctxt'')
              | _ -> (None, ctxt))
        | _ -> (None, ctxt))


  (* DONE: ERROR *)
  | Error -> (None, ctxt)

(* --------------------------------------------------------------------------
 * PROGRAMS
 * -------------------------------------------------------------------------- *)
let t_prog_extra_args args ctxt : (Tast.arg list) * (Tast.annotation list) =
  let { venv } = ctxt
  in let resolve_arg (arg: ty_from prog_arg) =
       match arg with
       | Error -> None
       | Arg{ var; ty; mut } ->
         let arg_dist = SMap.find var venv
         in begin
           match arg_dist with
           | HatVarDist{ var=var2 } ->
             if var=var2 && match ty with
               | ListTy _ -> not mut
               | _ -> true
             then let hat_var = resolve_hat_name var ctxt
               in let hat_var_arg = Tast.Arg{ var=Tast.Var hat_var
                                            ; is_ghost=true
                                            ; ty=tastty_of_astty (update_base ty (FloatTy ())) }
               in let hat_var_anno =
                    match ty with
                    | FloatTy _ -> []
                    | ListTy  _ -> [( Tast.Precondition
                                    , Tast.Prop(Tast.OpExp{
                                          left=Tast.CallExp{ func="Size"
                                                           ; args=[Tast.VarExp var] }
                                        ; right=Tast.CallExp{ func="Size"
                                                            ; args=[Tast.VarExp hat_var] }
                                        ; op=Tast.EqOp}))]
                    | _ -> raise (NotImplemented (__FILE__ ^" : "^ string_of_int __LINE__))
               in Some(hat_var_arg, hat_var_anno)
             else if var=var2
             then raise (DevMessage "Mutable star-typed lists are currently not supported")
             else raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__))
           | _ -> None
         end

  in let acc_init : (Tast.arg list) * (Tast.annotation list) = ([],[])
  in List.fold_left
    (fun (arg_acc, anno_acc) arg -> match resolve_arg arg with
       | None              -> (arg_acc, anno_acc)
       | Some(arg',annos') -> (arg'::arg_acc, annos' @ anno_acc))
    acc_init
    args

let rec t_prog_arg (arg: ty_from prog_arg) : Tast.arg =
  match arg with
  | Error -> raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__))
  | Arg{ var; ty; mut } -> Tast.Arg { var=Tast.Var var; is_ghost=false; ty=tastty_of_astty ty }

and t_prog_args (args : ty_from prog_arg list) : Tast.arg list =
  List.fold_right
    (fun (arg: ty_from prog_arg)
      (args: Tast.arg list) -> (t_prog_arg arg)::args)
    args
    []

let t_prog (prog: ty_from prog) : Tast.prog =
  match prog with
  | Error                                -> raise CompilationFail
  | Program { annos; stmts; stmts_dist_venv; name; args; ret_ty } ->
    let ctxt = { venv=stmts_dist_venv
               ; obligations=[]
               ; expected_dist=None
               }
    in let epsilon_arg = Tast.Arg{ var=Tast.Epsilon; is_ghost=false; ty=Tast.FloatTy }
    in let epsilon_anno = (Tast.Precondition, Tast.Prop(Tast.OpExp{ left=Tast.EpsilonExp
                                                                  ; right=Tast.FloatExp 0.0
                                                                  ; op=Tast.GtOp
                                                                  }))
    in let (extra_args, extra_annos) = t_prog_extra_args args ctxt
    in let args' =
         epsilon_arg :: t_prog_args args @ extra_args
    in let annos' = extra_annos @ epsilon_anno :: t_annos annos ctxt
    (* TODO: Add preconditions to constraints *)
    in let (stmts', ctxt') = t_stmts stmts ctxt
    in match stmts' with
    | None         -> raise CompilationFail
    | Some(stmts') ->
      let stmts'' = (Tast.DeclStmt{ ty=Tast.FloatTy
                                  ; var=Tast.EpsilonVar
                                  ; exp=Tast.FloatExp 0.0
                                  }
                    )::stmts'
      in Tast.Program { name=name
                      ; annos=annos'
                      ; stmts=stmts''
                      ; args=args'
                      ; ret_ty=tastty_of_astty ret_ty }
