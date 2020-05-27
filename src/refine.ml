open Env
open Ast
open Util

(* --------------------------------------------------------------------------
 * EXCEPTIONS
 * -------------------------------------------------------------------------- *)
open Exception

(* --------------------------------------------------------------------------
 * ENVIRONMENT
 * -------------------------------------------------------------------------- *)
type ty_from = ty_dist option ty
type ty_to = unit ty

type venv_value = { dist: dist; mut: bool }
and  venv = venv_value SMap.t

type ctxt = { venv: venv; vdeps: (string list * bool) SMap.t }

let update_venv (var: string) (data: venv_value) (ctxt: ctxt) : ctxt =
  let { venv; vdeps } = ctxt
  in let venv' = SMap.add var data venv
  in { venv=venv'; vdeps=vdeps }

let extract_disjoint_venv ({ venv=venv_new }: ctxt) ({ venv=venv_old; vdeps }: ctxt) : dist_venv * ctxt =
  let new_only_venv = venv_new |> SMap.filter (fun key _ -> not (SMap.mem key venv_old))
                               |> SMap.map (fun ({ dist }) -> dist)
  in let venv_old' = venv_old (* TODO: Renfiment rules to be applied here *)
  in (new_only_venv, { venv=venv_old'; vdeps })

let update_vdeps (var : string) (deps : string list) (ctxt: ctxt) : ctxt =
  let { venv; vdeps } = ctxt
  in let vdeps' = SMap.add var (deps, false) vdeps
  in { venv=venv; vdeps=vdeps' }

let mark_dependencies (dep : string) (ctxt: ctxt) : ctxt =
  let { venv; vdeps } = ctxt
  in let vdeps' = SMap.map (fun (deps, lock) -> (deps, lock||(List.exists (fun d -> d = dep) deps))) vdeps
  in { venv=venv; vdeps=vdeps' }

let is_locked (var: string) ({ venv; vdeps }: ctxt) : bool =
  match SMap.find_opt var vdeps with
  | None -> false
  | Some((deps, locked)) ->
    if locked
    then match SMap.find_opt var venv with
      | Some({ dist=HatVarDist{var=hatvar} }) ->
        if hatvar = var
        then false
        else raise (NotImplemented (__FILE__ ^" : "^ string_of_int __LINE__))
      | Some(_) -> true
      | None -> raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__))
    else false

(* --------------------------------------------------------------------------
 * HELPER FUNCTIONS
 * -------------------------------------------------------------------------- *)
let rec dist_of_ty (name: string) (ty: ty_from) : dist  =
  match ty with
  | Error                -> Error
  | ListTy(inner)        ->
    let dist' = dist_of_ty name inner
    in begin
      match dist' with
      | HatVarDist{ var; lnum; ty=ty' } ->
        if name = var
        then match ty' with
          | Some(ty') -> HatVarDist{ var=name; lnum=lnum; ty=Some(ListTy ty') }
          | _         -> raise (NotImplemented (__FILE__ ^" : "^ string_of_int __LINE__))
        else dist'
      | _ -> dist'
    end
  | IntTy dist
  | FloatTy dist         ->
    begin
      match dist with
      | Some(Dist(dist')) -> dist'
      | Some(SigmaDist)   -> HatVarDist{ var=name; lnum=None; ty=Some(FloatTy ()) }
      | _                 -> raise (NotImplemented (__FILE__ ^" : "^ string_of_int __LINE__))
    end
  | BoolTy               -> FloatDist 0.0

(* Variable dependencies *)
let rec extract_dependencies (exp: 'a exp) (ctxt: ctxt) : string list =
  let {venv} = ctxt
  in match exp with
  (* TODO: One can keep track of only mutable variables to minimize this size,
           but one would need to store `mut` then in venv. *)
  | VarExp{var} | HatVarExp{var} ->
    begin match SMap.find_opt var venv with
      | Some({mut}) -> if mut then [var] else []
      | None -> raise (DevMessage (__FILE__ ^" : "^ string_of_int __LINE__))
    end
  | OpExp{left; right} ->
    (extract_dependencies left ctxt)@(extract_dependencies right ctxt)
  | NotExp{exp} ->
    extract_dependencies exp ctxt
  | ConcatExp{elem; list} ->
    (extract_dependencies elem ctxt)@(extract_dependencies list ctxt)
  | TernaryExp{cond_exp; then_exp; else_exp} ->
    (extract_dependencies cond_exp ctxt)@
    (extract_dependencies then_exp ctxt)@
    (extract_dependencies else_exp ctxt)
  | SubExp{list;idx} ->
    (extract_dependencies list ctxt)@(extract_dependencies idx ctxt)
  | CallExp{args} ->
    List.fold_left (fun acc arg -> (extract_dependencies arg ctxt)@acc) [] args
  | _ -> []

let string_of_deps var ({vdeps}: ctxt) : string =
  match SMap.find_opt var vdeps with
  | None -> ""
  | Some((deps, _)) ->
    String.concat ", " (List.map (fun n -> "'"^n^"'") deps)

(* --------------------------------------------------------------------------
 * EXPRESSIONS
 * -------------------------------------------------------------------------- *)
let rec r_exp (exp : ty_from exp) (ctxt: ctxt) : ty_to exp =
  match exp with
  | EpsilonExp{lnum}    -> EpsilonExp{lnum=lnum}
  | EpsilonVarExp{lnum} -> EpsilonVarExp{lnum=lnum}
  | BoolExp b           -> BoolExp b
  | IntExp n            -> IntExp n
  | FloatExp n          -> FloatExp n
  | VarExp{ var; lnum; ty }   ->
    if is_locked var ctxt
    then ("Dependencies "^(string_of_deps var ctxt)^" of '"^var^"' have changed since it was declared. "^
          " Use * distance-type instead at declaration" |> print_error None
         ; Error)
    else VarExp{ var; lnum; ty=update_dist ty () }

    (* To be conservative we also have the same restriction for hat variables *)
  | HatVarExp{var; lnum} ->
    if is_locked var ctxt
    then ("Dependencies "^(string_of_deps var ctxt)^" of '"^var^"' have changed since it was declared. "^
          " Use * distance-type instead at declaration" |> print_error None
         ; Error)
    else HatVarExp{ lnum; var; ty=FloatTy () }

  | UMinusExp{ lnum; exp; ty } ->
    UMinusExp{ lnum=lnum; exp=r_exp exp ctxt; ty=update_dist ty () }

  | OpExp{lnum; left; right; op; ty} ->
    (match (r_exp left ctxt, r_exp right ctxt) with
     | (Error, _) | (_, Error) -> Error
     | (left', right') -> OpExp{lnum=lnum
                               ; left=left'
                               ; right=right'
                               ; op=op
                               ; ty=update_dist ty () })

  | NotExp{lnum; exp} ->
    (match r_exp exp ctxt with
     | Error -> Error
     | exp' -> NotExp{lnum=lnum; exp=exp'})

  | TernaryExp{cond_exp; then_lnum; then_exp; else_lnum; else_exp; ty} ->
    (match (r_exp cond_exp ctxt, r_exp then_exp ctxt, r_exp else_exp ctxt) with
     | (Error, _, _) | (_, Error, _) | (_, _, Error) -> Error
     | (cond_exp', then_exp', else_exp') -> TernaryExp{ cond_exp=cond_exp'
                                                      ; then_lnum=then_lnum
                                                      ; then_exp=then_exp'
                                                      ; else_lnum=else_lnum
                                                      ; else_exp=else_exp'
                                                      ; ty=update_dist ty ()
                                                      })

  | NilExp{lnum; ty} ->
    NilExp{ lnum=lnum; ty=update_dist ty () }

  | ConcatExp{lnum; elem; list; ty}  ->
    (match (r_exp elem ctxt, r_exp list ctxt) with
     | (Error, _) | (_, Error) -> Error
     | (elem', list') -> ConcatExp{lnum=lnum
                                  ; elem=elem'
                                  ; list=list'
                                  ; ty=update_dist ty ()
                                  })

  | SubExp{lnum; list; idx; ty}   ->
    (match (r_exp list ctxt, r_exp idx ctxt) with
     | (Error, _) | (_, Error) -> Error
     | (list', idx') -> SubExp{lnum=lnum
                              ; list=list'
                              ; idx=idx'
                              ; ty=update_dist ty ()
                              })

  | CallExp{lnum; func; args; ty} ->
    let args_init : (ty_to exp list) option = Some([])
    in let args' = List.fold_left
           (fun acc arg -> match (r_exp arg ctxt, acc) with
              | (Error, _) | (_, None) -> None
              | (arg', Some(args')) -> Some(arg'::args'))
           args_init
           args
    in (match args' with
        | Some(args') -> CallExp{ lnum=lnum
                                ; func=func
                                ; args=args'
                                ; ty=update_dist ty ()
                                }
        | None -> Error)
  | TypeCastExp{ lnum; to_ty; exp } ->
    TypeCastExp{ lnum=lnum; to_ty=to_ty; exp=r_exp exp ctxt }

  | Error -> Error

(* --------------------------------------------------------------------------
 * ANNOTATION
 * -------------------------------------------------------------------------- *)
let rec r_aexp (aexp : ty_from aexp) (ctxt: ctxt) : ty_to aexp option =
  match aexp with
  | Quantifier(aquant, vars, ty, aexp') ->
    let ctxt' = vars |> List.fold_left
                  (fun acc_ctxt var -> acc_ctxt |> update_venv
                                         var
                                         { dist=(FloatDist 0.0); mut=false})
                  ctxt
    in begin
      match r_aexp aexp' ctxt' with
      | None        -> None
      | Some(aexp') -> Some(Quantifier(aquant
                                      , vars
                                      , update_dist ty ()
                                      , aexp'))
    end

  | Prop(exp) ->
    begin
      match r_exp exp ctxt with
      | Error -> None
      | exp'  -> Some(Prop(exp'))
    end

let rec r_anno (ctxt: ctxt) (anno: ty_from annotation) : ty_to annotation =
  match anno with
  | Error -> Error
  | Annotation{lnum; av; aexp} ->
    begin
      match r_aexp aexp ctxt with
      | Some(aexp') -> Annotation{lnum=lnum; av=av; aexp=aexp'}
      | None -> Error
    end

(* TODO: On error return [Error] *)
and r_annos (annos: ty_from annotation list) (ctxt: ctxt) : ty_to annotation list =
  List.map (r_anno ctxt) annos


(* --------------------------------------------------------------------------
 * STATEMENTS
 * -------------------------------------------------------------------------- *)
let rec r_stmts (stmts : ty_from stmt list) (ctxt: ctxt) : ty_to stmt list * ctxt =
  let (stmts_rev, ctxt') = stmts |> List.fold_left
                             (fun ((cs, ctxt') : ty_to stmt list * ctxt) (c: ty_from stmt) ->
                                let (c', ctxt'') = r_stmt c ctxt'
                                in match (cs, c') with
                                | ([Error], _) -> ([Error], ctxt'')
                                | (_, Error)   -> ([Error], ctxt'')
                                | _            -> (c'::cs , ctxt''))
                             ([], ctxt)
  in (List.rev stmts_rev, ctxt')


and r_stmt (stmt : ty_from stmt) (ctxt: ctxt) : ty_to stmt * ctxt =
  match stmt with
  (* DONE: SKIP *)
  | SkipStmt{lnum} -> (SkipStmt{lnum=lnum}, ctxt)

  (* DONE: ASSIGNMENT | TODO: Test *)
  | AssignStmt{ lnum; var; exp } ->
    let exp' = r_exp exp ctxt
    in (AssignStmt{ lnum=lnum; var=var; exp=exp' }
       , mark_dependencies var ctxt)

  (* DONE: DECLARATION | TODO: Test *)
  | DeclStmt{ lnum; ty; var; exp; mut } ->
    let dist' = dist_of_ty var ty
    in let ty' = update_dist ty ()
    in let exp' = r_exp exp ctxt
    in (match exp' with
        | Error -> (Error, ctxt)
        | CallExp{lnum; func="Lap"; args} ->
          let deps = extract_dependencies exp' ctxt
          in (DeclStmt{lnum; ty=ty'; var; exp=exp'; mut}
             , ctxt |> update_venv var { dist=dist'; mut }
                    |> update_vdeps var deps)
        | _ ->
          (DeclStmt{lnum; ty=ty'; var; exp=exp'; mut}
          , ctxt |> update_venv var { dist=dist'; mut } ))

  (* DONE: RETURN *)
  | ReturnStmt{lnum; exp} -> (ReturnStmt{ lnum=lnum; exp=r_exp exp ctxt }, ctxt)

  (* DONE: IF THEN ELSE *)
  | IfStmt{ cond_lnum; cond_exp
          ; then_lnum; then_body; then_dist_venv
          ; else_lnum; else_body; else_dist_venv } ->
    let cond_exp' = r_exp cond_exp ctxt
    in let (then_body', then_ctxt) = r_stmts then_body ctxt
    in let (then_dist_venv', ctxt') = extract_disjoint_venv then_ctxt ctxt
    in let (else_body', else_ctxt) = r_stmts else_body ctxt
    in let (else_dist_venv', ctxt'') = extract_disjoint_venv else_ctxt ctxt'
    in (IfStmt{ cond_lnum
              ; cond_exp=cond_exp'
              ; then_lnum
              ; then_body=then_body'
              ; then_dist_venv=then_dist_venv'
              ; else_lnum
              ; else_body=else_body'
              ; else_dist_venv=else_dist_venv'
              }
       , ctxt'')

  (* DONE: WHILE *)
  | WhileStmt{ lnum; cond_exp; annos; body; body_dist_venv } ->
    let cond_exp' = r_exp cond_exp ctxt
    in let (body', body_ctxt) = r_stmts body ctxt
    in let (body_dist_venv', ctxt') = extract_disjoint_venv body_ctxt ctxt
    in (WhileStmt{ lnum=lnum
                 ; cond_exp=cond_exp'
                 ; annos=r_annos annos ctxt
                 ; body=body'
                 ; body_dist_venv=body_dist_venv'
                 }
       , ctxt')

  (* DONE: ERROR *)
  | Error -> (Error, ctxt)


(* --------------------------------------------------------------------------
 * PROGRAMS
 * -------------------------------------------------------------------------- *)
let rec r_prog_arg (arg: ty_from prog_arg) (ctxt: ctxt) : ty_to prog_arg * ctxt =
  match arg with
  | Error                -> (Error, ctxt)
  | Arg { var; ty; mut } ->
    let dist' = dist_of_ty var ty
    in let ty' = update_dist ty ()
    in (Arg { var; ty=ty'; mut }
       , update_venv var { dist=dist'; mut } ctxt)

and r_prog_args (args: ty_from prog_arg list) (ctxt: ctxt) : ty_to prog_arg list * ctxt =
  List.fold_right
    (fun (arg : ty_from prog_arg) ((args', ctxt') : ty_to prog_arg list * ctxt) ->
       let (arg', ctxt'') = r_prog_arg arg ctxt'
       in match (args', arg) with
       | ([Error], _) | (_, Error) -> ([Error], ctxt'')
       | _                         -> (arg'::args', ctxt''))
    args
    ([], ctxt)


let r_prog (prog : ty_from prog) : ty_to prog =
  let ctxt: ctxt = { venv=SMap.empty; vdeps=SMap.empty }
  in match prog with
  | Error -> Error
  | Program { lnum; annos; stmts; stmts_dist_venv; name; args; ret_ty } ->
    let (args' , ctxt')  = r_prog_args args ctxt
    in let (stmts', { venv }) = r_stmts stmts ctxt'
    in match (args', stmts') with
    | ([Error], _) | (_, [Error]) -> Error
    | _ -> (Program { lnum
                    ; annos=r_annos annos ctxt'
                    ; stmts=stmts'
                    ; stmts_dist_venv=venv |> SMap.map (fun ({ dist }) -> dist)
                    ; name
                    ; args=args'
                    ; ret_ty=update_dist ret_ty ()
                    }
           )

