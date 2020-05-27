open Tast
open Exception

type ctxt = { indent: string; print_annos: bool }

let init_ctxt = { indent=""; print_annos=true }

let indent_ctxt ctxt =
  let { indent; print_annos } = ctxt
  in { indent=indent^"  "; print_annos=print_annos }

(* --------------------------------------------------------------------------
 * TYPES
 * -------------------------------------------------------------------------- *)
let rec pty_ty ty : string =
  match ty with
  | FloatTy       -> "real"
  | IntTy         -> "int"
  | BoolTy        -> "bool"
  | ListTy(inner) -> "seq<"^(pty_ty inner)^">"

(* --------------------------------------------------------------------------
 * EXPRESSIONS
 * -------------------------------------------------------------------------- *)

let pty_op (op: oper) : string =
  match op with
  | PlusOp -> "+"
  | MinusOp -> "-"
  | TimesOp -> "*"
  | DivideOp -> "/"
  | ModuloOp -> "%"
  | EqOp -> "=="
  | LtOp -> "<"
  | LeOp -> "<="
  | GtOp -> ">"
  | GeOp -> ">="
  | AndOp -> "&&"
  | OrOp -> "||"
  | ImpliesOp -> "==>"

let rec pty_exp (exp : exp) : string =
  match exp with
  | EpsilonExp ->
    "epsilon"
  | EpsilonVarExp ->
    "v_epsilon"
  | BoolExp(b)    ->
    string_of_bool b
  | FloatExp(n)     ->
    (string_of_float n)^"0"
  | IntExp(n)     ->
    (string_of_int n)
  | VarExp(v)     ->
    v
  | UMinusExp{exp} ->
    "-"^(pty_exp exp)
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
    "if "^(pty_exp cond_exp)^" then "^(pty_exp then_exp)^" else "^(pty_exp else_exp)
  (* List expressions *)
  | NilExp  ->
    "[]"
  | ConcatExp{elem; list}  ->
    "["^(pty_exp elem)^"]+"^(pty_exp list)
  | SubExp{list; idx}   ->
    (match list with
     | ConcatExp(_) -> "("^(pty_exp list)^")"
     | _            -> pty_exp list
    )^"["^(pty_exp idx)^"]"
  (* Functions *)
  | CallExp{func; args} ->
    let args' = args |> List.map (fun a -> pty_exp a)
    in (match func with
        | "Size" -> "|"^(List.nth args' 0)^"|"
        | _ -> func^"("^(String.concat ", " args')^")" )
  | TypeCastExp{to_ty; exp} ->
    let inner_paren = match exp with
      | FloatExp(_) | IntExp(_) | VarExp(_) | EpsilonExp | EpsilonVarExp | UMinusExp(_) ->
        (pty_exp exp)
      | _ -> "("^(pty_exp exp)^")"
    in "("^inner_paren^" as "^(pty_ty to_ty)^")"

(* --------------------------------------------------------------------------
 * ANNOTATION
 * -------------------------------------------------------------------------- *)
let pty_anno ((avariant, aexp): annotation) : string =
  let avariant' = match avariant with
                  | Precondition  -> "requires"
                  | Postcondition -> "ensures"
                  | Invariant     -> "invariant"
                  | Termination   -> "decreases"
  in let rec pty_aexp aexp = match aexp with
    | Quantifier (quantifier,vars,ty,aexp') ->
      let pty_quantifier = match quantifier with
        | Forall -> "forall"
        | Exists -> "exists"
      in let rec vars' = String.concat ", " vars
      in pty_quantifier^" "^(vars')^": "^(pty_ty ty)^" :: "^(pty_aexp aexp')
    | Prop(e) ->
      pty_exp e
  in avariant'^" "^(pty_aexp aexp)

(* --------------------------------------------------------------------------
 * STATEMENTS
 * -------------------------------------------------------------------------- *)
let rec pty_stmts (stmts : stmt list) (ctxt: ctxt) : string =
  stmts
    |> List.filter ( fun c -> match c with
                              | SkipStmt -> false
                              | _ -> true )
    |> List.fold_left
      (fun (acc: string) (c: stmt) -> acc ^ (pty_stmt c ctxt)  ^ "\n")
      ""

and pty_assignee (var: assignee) : string =
  match var with
  | Var(v) -> v
  | GhostVar(v) -> v
  | EpsilonVar -> "v_epsilon"

and pty_stmt (stmt : stmt) (ctxt: ctxt) : string =
  let { indent; print_annos } = ctxt
  in match stmt with
  | SkipStmt ->
    ("'Skip' statement not printed to Dafny" |> print_warning None; "")
  | HavocStmt{ var } ->
    let havoc_line_1 = "var "^var^" :| 0.0 <= "^var^";\n"
    in let havoc_line_2 = "if * { "^var^" := "^var^"; } else { "^var^" := -"^var^"; }"
    in indent^havoc_line_1^indent^havoc_line_2
  | AssignStmt{ var; exp } ->
    indent^(pty_assignee var)^" := "^(pty_exp exp)^";"
  | DeclStmt{ ty; var; exp } ->
    let decl_prefix = match var with
      | Var(_) -> "var"
      | EpsilonVar | GhostVar(_) -> "ghost var"

    in indent^decl_prefix^" "^(pty_assignee var)^" : "^(pty_ty ty)^" := "^(pty_exp exp)^";"

  | ReturnStmt{ exp } ->
    indent^"return "^(pty_exp exp)^";"
  | IfStmt{ cond_exp; then_body; else_body } ->
    let then_string = "{\n"^(pty_stmts then_body (indent_ctxt ctxt))^indent^"}"
    in let else_string = match else_body with
        | [] | [SkipStmt] -> ""
        | _                  -> " else {\n"^(pty_stmts else_body (indent_ctxt ctxt))^indent^"}"
    in indent^"if "^(pty_exp cond_exp)^" "^then_string^else_string
  | WhileStmt{ cond_exp; annos; body } ->
    let annos' = if print_annos
         then (List.fold_left
                (fun acc anno -> acc^indent^"  "^(pty_anno anno)^"\n")
                ""
                annos)
         else ""
    in indent^"while ("^(pty_exp cond_exp)^")\n"^annos'^
       indent^"{\n"^(pty_stmts body (indent_ctxt ctxt))^indent^"}"
  | Comment(comment) ->
    indent^"// "^comment
  | Assert(exp, comment_opt) ->
    let comment_string = match comment_opt with
      | None -> ""
      | Some(comment) -> " // "^comment
    in indent^"assert "^(pty_exp exp)^";"^comment_string

(* --------------------------------------------------------------------------
 * PROGRAM
 * -------------------------------------------------------------------------- *)

(* TODO: Prepend absolute function and havoc function *)

let pty_prog (prog : prog) (ctxt: ctxt) : string =
  let { indent; print_annos } = ctxt
  in let Program { annos; stmts; name; args; ret_ty } = prog
  in let annos' =
         if print_annos
         then List.fold_left (fun acc anno -> acc^indent^"  "^(pty_anno anno)^"\n") "" annos
         else ""
  in let pty_arg arg =
       let Arg {var; is_ghost; ty} = arg
       in let var' = match var with
       | Var var -> var
       | Epsilon -> "epsilon"
       in (if is_ghost then "ghost " else "")^var'^" : "^(pty_ty ty)
  in let rec pty_args args = match args with
      | []     -> ""
      | a::[]  -> pty_arg a
      | a::ax  -> (pty_arg a)^", "^(pty_args ax)
  in indent^"method "^name^"("^(pty_args args)^") returns (_:"^(pty_ty ret_ty)^")\n"^
       annos'^indent^"{\n"^(pty_stmts stmts (indent_ctxt ctxt))^indent^"}"
