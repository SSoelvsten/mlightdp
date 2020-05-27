(* --------------------------------------------------------------------------
 * TYPES
 * -------------------------------------------------------------------------- *)
type ty = IntTy
        | FloatTy
        | BoolTy
        | ListTy of ty

(* --------------------------------------------------------------------------
 * EXPRESSIONS
 * -------------------------------------------------------------------------- *)
type oper = PlusOp | MinusOp | TimesOp | DivideOp
          | ModuloOp
          | EqOp | LtOp | LeOp | GtOp | GeOp
          | AndOp | OrOp | ImpliesOp

type exp = EpsilonExp
         | EpsilonVarExp
         | BoolExp    of bool
         | IntExp     of int
         | FloatExp   of float
         | VarExp     of string
         | UMinusExp  of { exp: exp }
         | OpExp      of { left: exp; right: exp; op: oper }
         | NotExp     of { exp: exp }
         | NilExp
         | ConcatExp   of { elem: exp; list: exp }
         | TernaryExp  of { cond_exp: exp; then_exp: exp; else_exp: exp }
         | SubExp      of { list: exp; idx: exp }
         | CallExp     of { func: string; args: exp list }
         | TypeCastExp of { to_ty: ty; exp: exp }


(* --------------------------------------------------------------------------
 * ANNOTATION
 * -------------------------------------------------------------------------- *)
type annotation = avariant * aexp

and avariant = Precondition | Postcondition | Invariant | Termination

and aexp = Quantifier of aquant * string list * ty * aexp
         | Prop of exp

and aquant = Forall | Exists


(* --------------------------------------------------------------------------
 * STATEMENTS
 * -------------------------------------------------------------------------- *)
type assignee = Var of string
              | GhostVar of string
              | EpsilonVar

type stmt = SkipStmt
          | HavocStmt  of { var : string }
          | AssignStmt of { var: assignee; exp: exp }
          | DeclStmt   of { ty: ty; var: assignee; exp: exp }
          | ReturnStmt of { exp: exp }
          | IfStmt     of { cond_exp: exp; then_body: stmt list; else_body: stmt list }
          | WhileStmt  of { cond_exp: exp; annos: annotation list; body: stmt list }
          | Comment    of string
          | Assert     of exp * string option

(* --------------------------------------------------------------------------
 * PROGRAM
 * -------------------------------------------------------------------------- *)
type prog = Program of { annos: annotation list
                       ; stmts: stmt list
                       ; name: string
                       ; args: arg list
                       ; ret_ty: ty }

and arg_name = Var of string
             | Epsilon

and arg = Arg of { var: arg_name; is_ghost: bool; ty: ty }
