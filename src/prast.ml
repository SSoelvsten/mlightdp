open Ast
open Exception

type ctxt = { indent: string; print_annos: bool }

let init_ctxt = { indent=""; print_annos=false }

let indent_ctxt ctxt =
  let { indent; print_annos } = ctxt
  in { indent=indent^"  "; print_annos=print_annos }

(* --------------------------------------------------------------------------
 * TYPES
 * -------------------------------------------------------------------------- *)
let rec pty_ty (ty: 'd ty) : string =
  match ty with
  | IntTy(_)      -> "int"
  | FloatTy(_)    -> "float"
  | BoolTy        -> "bool"
  | ListTy(inner) -> "list("^(pty_ty inner)^")"
  | Error         -> "?"

(* --------------------------------------------------------------------------
 * EXPRESSIONS
 * -------------------------------------------------------------------------- *)
let pty_op (op: oper) : string =
  match op with
  | PlusOp -> "+"
  | MinusOp -> "-"
  | TimesOp -> "×"
  | DivideOp -> "/"
  | ModuloOp -> "%"
  | EqOp -> "="
  | LtOp -> "<"
  | LeOp -> "≤"
  | GtOp -> ">"
  | GeOp -> "≥"
  | AndOp -> "&&"
  | OrOp -> "||"
  | ImpliesOp -> "⇒"

let rec pty_exp (exp : 'a exp) : string =
  match exp with
  | IntExp(n)     ->
    string_of_int n

  | FloatExp(n)     ->
    string_of_float n

  | EpsilonExp(_) ->
    "ε"

  | EpsilonVarExp(_) ->
    "Δε"

  | BoolExp(b)    ->
    string_of_bool b

  | VarExp{var}     ->
    var

  | HatVarExp{var}  ->
    "^"^var

  | UMinusExp{exp} ->
    begin
      match exp with
      | IntExp(_) | FloatExp(_) -> "-"^(pty_exp exp)
      | _ -> "-("^(pty_exp exp)^")"
    end

  | OpExp{left; right; op} ->
    let is_precedence_conflict inner_op =
      match op with
      | PlusOp | MinusOp -> false
      | TimesOp | DivideOp ->
        (match inner_op with
         | PlusOp | MinusOp | DivideOp -> true
         | _ -> false)
      | ImpliesOp -> false
      | AndOp ->
        (match inner_op with
         | ImpliesOp -> true
         | _ -> false)
      | OrOp ->
        (match inner_op with
         | AndOp | ImpliesOp -> true
         | _ -> false)
      | _ -> false
    in let left' = match left with
        | TernaryExp(_) -> "("^(pty_exp left)^")"
        | OpExp{ op=op' } ->
          if op' |> is_precedence_conflict
          then "("^(pty_exp left)^")"
          else begin
            match (op', op) with
            | (ImpliesOp, ImpliesOp) -> "("^(pty_exp left)^")"
            | _ -> pty_exp left
            end
        | _ -> pty_exp left
    in let right' = match right with
        | TernaryExp(_) -> "("^(pty_exp right)^")"
        | OpExp{ op=op' } ->
          if op' |> is_precedence_conflict
          then "("^(pty_exp right)^")"
          else begin
            match (op, op') with
            | (ModuloOp, ModuloOp) -> "("^(pty_exp right)^")"
            | _ -> pty_exp right
          end
        | _ -> pty_exp right
    in left'^" "^(pty_op op)^" "^right'

  | NotExp{exp} ->
    "!"^(match exp with
        | OpExp(_) | TernaryExp(_) -> "("^(pty_exp exp)^")"
        | _                        -> pty_exp exp)

  | TernaryExp{cond_exp; then_exp; else_exp} ->
    (pty_exp cond_exp)^" ? "^(pty_exp then_exp)^" : "^(pty_exp else_exp)

  (* List expressions *)
  | NilExp(_)  ->
    "[]"

  | ConcatExp{elem; list}  ->
    (pty_exp elem)^"::"^(pty_exp list)

  | SubExp{list; idx}   ->
    (match list with
     | ConcatExp(_) -> "("^(pty_exp list)^")"
     | _            -> pty_exp list
    )^"["^(pty_exp idx)^"]"

  (* Functions *)
  | CallExp{func; args} ->
    let rec pty_args args = match args with
      | []    -> ""
      | a::[]  -> pty_exp a
      | a::ax -> (pty_exp a)^", "^(pty_args ax)
    in func^"("^(pty_args args)^")"

  (* Typecasting *)
  | TypeCastExp{ to_ty; exp } ->
    "("^(pty_exp exp)^" as "^(pty_ty to_ty)^")"

  (* Error handling - propagate error upwards *)
  | Error -> "_"

(* --------------------------------------------------------------------------
 * ANNOTATION
 * -------------------------------------------------------------------------- *)
let pty_anno (a: 'a annotation): string =
  let string_of_av av = match av with
    | Invariant  -> "invariant"
    | Termination -> "termination"
    | Precondition -> "precondition"
    | Postcondition -> "postcondition"
  in let rec pty_aexp aexp = match aexp with
    | Quantifier (quantifier,vars,_,aexp') ->
      let pty_quantifier = match quantifier with
        | Forall -> "∀"
        | Exists -> "∃"
      in let rec pty_vars vars = match vars with
        | []    -> ""
        | a::ax -> a^" "^(pty_vars ax)
      in let deliminator = match aexp' with
          | Prop(_) -> ": "
          | _       -> ""
      in pty_quantifier^(pty_vars vars)^deliminator^(pty_aexp aexp')
    | Prop(e) ->
      pty_exp e
  in match a with
  | Annotation{av; aexp} -> (string_of_av av)^" "^(pty_aexp aexp)
  | Error -> "_"

(* --------------------------------------------------------------------------
 * STATEMENTS
 * -------------------------------------------------------------------------- *)
let rec pty_stmts (stmts : 'a stmt list) (ctxt: ctxt) : string =
  stmts |> List.fold_left
    (fun (acc: string) (c: 'a stmt) -> acc ^ ";\n" ^ (pty_stmt c ctxt))
    ""

and pty_stmt (stmt : 'a stmt) (ctxt: ctxt) : string =
  let { indent; print_annos } = ctxt
  in match stmt with
  | SkipStmt(_) ->
    "Skip"
  | AssignStmt{ var; exp } ->
    var^" = "^(pty_exp exp)
  | DeclStmt{ var; exp; mut } ->
    "let "^(if mut then "mut " else "")^var^" = "^(pty_exp exp)
  | ReturnStmt{ exp } ->
    "return "^(pty_exp exp)
  | IfStmt{ cond_exp; then_body; else_body } ->
    let then_string = "{\n"^(pty_stmts then_body (indent_ctxt ctxt))^(indent^"}")
    in let else_string = match else_body with
        | [] | [SkipStmt(_)] -> ""
        | _                  -> "else {\n"^(pty_stmts else_body (indent_ctxt ctxt))^(indent^"}")
    in indent^"if ("^(pty_exp cond_exp)^")"^then_string^else_string
  | WhileStmt{ cond_exp; annos; body } ->
    let annos' = if print_annos
      then (List.fold_left (fun acc anno -> acc^indent^(pty_anno anno)^"\n") "" annos)
      else ""
    in annos'^indent^"while ("^(pty_exp cond_exp)^") {\n"^(pty_stmts body (indent_ctxt ctxt))^"}"
  | Error -> indent^"_;"


(* --------------------------------------------------------------------------
 * PROGRAMS
 * -------------------------------------------------------------------------- *)
let pty_prog (prog : 'a prog) (ctxt: ctxt) : string =
  let { indent; print_annos } = ctxt
  in match prog with
  | Program { annos; stmts; name; args; ret_ty } ->
    let annos' = if print_annos
         then List.fold_left (fun acc anno -> acc^indent^(pty_anno anno)^"\n") "" annos
         else ""
    in let pty_arg arg = match arg with
      | Arg {var; ty; mut} -> (if mut then "mut " else "")^var
      | Error              -> "_"
    in let rec pty_args args = match args with
      | []     -> ""
      | a::[]  -> pty_arg a
      | a::ax  -> (pty_arg a)^", "^(pty_args ax)
    in annos'^indent^name^"("^(pty_args args)^") {\n"^(pty_stmts stmts (indent_ctxt ctxt))^(indent^"}")

  | Error -> "_"
