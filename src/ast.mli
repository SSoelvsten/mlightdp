open Env

type lnum = int option

type oper = PlusOp | MinusOp | TimesOp | DivideOp
          | ModuloOp
          | EqOp | LtOp | LeOp | GtOp | GeOp
          | AndOp | OrOp | ImpliesOp

(* --------------------------------------------------------------------------
 * TYPES AND THEIR DISTANCES
 * -------------------------------------------------------------------------- *)
type 'd ty = IntTy   of 'd
           | FloatTy of 'd
           | BoolTy
           | ListTy  of 'd ty
           | Error

type dist = EpsilonDist of { lnum: lnum }
          | IntDist     of int
          | FloatDist   of float
          | VarDist     of { var: string; lnum: lnum; ty: unit ty option }
          | HatVarDist  of { var: string; lnum: lnum; ty: unit ty option }
          | DVarDist    of string
          | UMinusDist  of { lnum: lnum; dist: dist; ty: unit ty option }
          | OpDist      of { lnum: lnum
                           ; left: dist
                           ; right: dist
                           ; op: oper
                           ; ty: unit ty option
                           }
          | SubDist     of { lnum: lnum
                           ; list: dist
                           ; idx: dist
                           ; ty: unit ty option
                           }
          (* | TODO: NotExp of { exp: exp }                            *)
          | TernaryDist of { cond_dist: dist
                           ; then_lnum: lnum
                           ; then_dist: dist
                           ; else_lnum: lnum
                           ; else_dist: dist
                           ; ty: unit ty option
                           }
          (* | TODO: ? CallExp of { func: string; args: exp list }     *)
          | TypeCastDist of { dist: dist; to_ty: unit ty }
          | Error

and ty_dist = SigmaDist | Dist of dist

(* --------------------------------------------------------------------------
 * EXPRESSIONS
 * -------------------------------------------------------------------------- *)
type 't exp = EpsilonExp    of { lnum: lnum }
            | EpsilonVarExp of { lnum: lnum }
            | BoolExp       of bool
            | IntExp        of int
            | FloatExp      of float
            (* TODO: Place lnum here *)
            | VarExp        of { var: string; lnum: lnum; ty: 't }
            | HatVarExp     of { var: string; lnum: lnum; ty: 't }
            | UMinusExp     of { lnum: lnum
                               ; exp: 't exp
                               ; ty: 't }
            | OpExp         of { lnum: lnum
                               ; left: 't exp
                               ; right: 't exp
                               ; op: oper
                               ; ty: 't }
            | NotExp        of { lnum: lnum; exp: 't exp }
            | TernaryExp    of { cond_exp: 't exp
                               ; then_lnum: lnum
                               ; then_exp: 't exp
                               ; else_lnum: lnum
                               ; else_exp: 't exp
                               ; ty: 't }
            | NilExp        of { lnum: lnum; ty: 't }
            | ConcatExp     of { lnum: lnum
                               ; elem: 't exp
                               ; list: 't exp
                               ; ty : 't }
            | SubExp        of { lnum: lnum
                               ; list: 't exp
                               ; idx: 't exp
                               ; ty : 't }
            | CallExp       of { lnum: lnum
                               ; func: string
                               ; args: 't exp list
                               ; ty: 't }
            | TypeCastExp   of { to_ty: unit ty
                               ; exp: 't exp
                               ; lnum: lnum
                               }
            | Error

(* --------------------------------------------------------------------------
 * ANNOTATION
 * -------------------------------------------------------------------------- *)
type 't annotation = Annotation of { lnum: lnum; av: avariant; aexp: 't aexp }
                   | Error

and avariant = Invariant | Termination | Precondition | Postcondition

and 't aexp = Quantifier of aquant * string list * 't * 't aexp
         | Prop of 't exp

and aquant = Forall | Exists

(* --------------------------------------------------------------------------
 * DISTANCE ENVIRONMENT (allows scoping of variables across parses)
 * -------------------------------------------------------------------------- *)
type dist_venv = dist SMap.t

(* --------------------------------------------------------------------------
 * STATEMENTS
 * -------------------------------------------------------------------------- *)
type 't stmt = SkipStmt   of { lnum: lnum }
             | AssignStmt of { lnum: lnum; var: string; exp: 't exp }
             | DeclStmt   of { lnum: lnum
                             ; ty: 't
                             ; var: string
                             ; exp: 't exp
                             ; mut: bool
                             }
             | ReturnStmt of { lnum: lnum; exp: 't exp }
             | IfStmt     of { cond_lnum: lnum
                             ; cond_exp: 't exp
                             ; then_lnum: lnum
                             ; then_body: 't stmt list
                             ; then_dist_venv: dist_venv
                             ; else_lnum: lnum
                             ; else_body: 't stmt list
                             ; else_dist_venv: dist_venv
                             }
             | WhileStmt  of { lnum: lnum
                             ; cond_exp: 't exp
                             ; annos: 't annotation list
                             ; body: 't stmt list
                             ; body_dist_venv: dist_venv
                             }
             | Error

(* --------------------------------------------------------------------------
 * PROGRAM
 * -------------------------------------------------------------------------- *)
type 't prog_arg = Arg of { var: string; ty: 't; mut: bool }
                 | Error

type 't prog = Program of { lnum: lnum
                          ; annos: 't annotation list
                          ; stmts: 't stmt list
                          ; stmts_dist_venv: dist_venv
                          ; name: string
                          ; args: 't prog_arg list
                          ; ret_ty: 't
                          }
             | Error
