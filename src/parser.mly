%{
  open Env
  open Ast
  open Exception

  let simple_type_resolve (identifier: string) (dist: 'd) : 'd ty =
    match identifier with
       | "int"    -> IntTy(dist)
       | "float"  -> FloatTy(dist)
       | "bool"   ->
          begin
            match dist with
            | None | Some(Dist(IntDist 0)) | Some(Dist(FloatDist 0.0)) -> BoolTy
            | _ -> "Type 'bool' cannot have non-zero distance" |> print_error None; Error
          end
       | _ -> "Unknown type: " ^ identifier |> print_error None; Error

  let constructor_type_resolve (identifier: string) (arg: 'd ty) (dist: 'd) : 'd ty =
    match identifier with
    | "list"  ->
       begin
         match dist with
         | None | Some(Dist(IntDist 0)) | Some(Dist(FloatDist 0.0)) -> ListTy(arg)
         | _ -> "Type 'list' cannot have non-zero distance" |> print_error None; Error
       end
    | _ -> "Unknown type constructor: " ^ identifier |> print_error None; Error

  let is_some (m: unit option) =
    match m with
    | None -> false
    | _    -> true

  let nil_if_none (xs: 'a list option) =
    match xs with
    | None     -> []
    | Some(xs) -> xs

  let concat_if_some (x: 'a) (xs: 'a list option) = x :: (nil_if_none xs)
%}

/* Lexing tokens */
%token <string> IDENTIFIER
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token <int> DIST
%token <int> LPAREN RPAREN LBRACKET RBRACKET LSQUAREB RSQUAREB NIL
%token <int> PLUS MINUS STAR DIV NOT CONCAT AND OR IMPLIES MODULO
%token <int> EQUALS NEQUALS LESS GREATER LESSEQ GREATEQ
%token <int> LET ASSIGN WHILE IF ELSE SKIP RETURN
%token <int> COLON QMARK
%token MUT
%token <int> PRECONDITION POSTCONDITION INVARIANT TERMINATION EPSILON EPSILONVAR
%token FORALL EXISTS
%token EOC EOF COMMA

/* Precedence, associativity (lowest -> highest) */
%right      CONCAT
%right      IMPLIES
%left       OR
%left       AND
%right      QMARK COLON
%nonassoc   EQUALS NEQUALS LESS LESSEQ GREATER GREATEQ
%left       NOT
%left       MODULO
%left       PLUS MINUS
%left       STAR DIV
%nonassoc   UMINUS
%nonassoc   LSQUAREB
%nonassoc   DIST

/* Parsing base */
%type <Ast.ty_dist option Ast.ty> ty

%start main_exp
%type <(Ast.ty_dist option Ast.ty option) Ast.exp> main_exp

%start main_stmt
%type <(Ast.ty_dist option Ast.ty option) Ast.stmt list> main_stmt

%start main_prog
%type <(Ast.ty_dist option Ast.ty option) Ast.prog> main_prog

%%

(* --------------------------------------------------------------------------
 * START SYMBOLS
 * -------------------------------------------------------------------------- *)
main_exp:  e=exp EOF                                        {e}
main_stmt: c=stmt EOF                                       {c}
main_prog: p=prog EOF                                       {p}

%inline op: lnum=PLUS                                       { (lnum, PlusOp) }
          | lnum=MINUS                                      { (lnum, MinusOp) }
          | lnum=STAR                                       { (lnum, TimesOp) }
          | lnum=DIV                                        { (lnum, DivideOp) }
          | lnum=MODULO                                     { (lnum, ModuloOp) }
          | lnum=EQUALS                                     { (lnum, EqOp) }
          | lnum=LESS                                       { (lnum, LtOp) }
          | lnum=LESSEQ                                     { (lnum, LeOp) }
          | lnum=GREATER                                    { (lnum, GtOp) }
          | lnum=GREATEQ                                    { (lnum, GeOp) }
          | lnum=AND                                        { (lnum, AndOp) }
          | lnum=OR                                         { (lnum, OrOp) }
          | lnum=IMPLIES                                    { (lnum, ImpliesOp) }

(* --------------------------------------------------------------------------
 * TYPES AND THEIR DISTANCES
 * -------------------------------------------------------------------------- *)
(* Use this one together with ? for optionals *)
ty_o: COLON ty=ty                                           { ty }

ty: i=IDENTIFIER ta=ty_align?                               { simple_type_resolve i ta }
  | i=IDENTIFIER LPAREN t=ty RPAREN ta=ty_align?            { constructor_type_resolve i t ta }

ty_align: LSQUAREB t=ty_base RSQUAREB                       { t }
        | LSQUAREB t1=ty_base COMMA t2=ty_base RSQUAREB     { raise (NotImplemented "We do not support shadow distances (yet?)") }

ty_base: STAR                                               { SigmaDist }
       | d=dist                                             { Dist(d) }

dist: n=INT                                                 { IntDist n }
    | n=FLOAT                                               { FloatDist n }
    | i=IDENTIFIER                                          { VarDist{ var=i; lnum=None; ty=None } }
    | l=EPSILON                                             { EpsilonDist{ lnum=Some(l) } }
    | l=EPSILONVAR                                          { ("v_epsilon is not allowed to be referenced in a distance." |> print_error (Some l)); Error }
    | d1=dist l1=QMARK d2=dist l2=COLON d3=dist             { TernaryDist{ cond_dist=d1
                                                                         ; then_lnum=Some(l1)
                                                                         ; then_dist=d2
                                                                         ; else_lnum=Some(l2)
                                                                         ; else_dist=d3
                                                                         ; ty=None} }
    | d1=dist o=op d2=dist                                  { let (lnum, op) = o
                                                              in OpDist{ lnum=Some(lnum)
                                                                       ; left=d1
                                                                       ; right=d2
                                                                       ; op=op
                                                                       ; ty=None} }
    | l=MINUS d=dist %prec UMINUS                           { UMinusDist{ lnum=Some(l)
                                                                        ; dist=d
                                                                        ; ty=None} }
    | LPAREN d=dist RPAREN                                  { d }
    | d=dist_hat                                            { d }
    | d1=dist l=LSQUAREB d2=dist RSQUAREB                   { SubDist{ lnum=Some(l)
                                                                     ; list=d1
                                                                     ; idx=d2
                                                                     ; ty=None } }
    (* Unsupported in distances? *)
    | IDENTIFIER LPAREN dist_call_args? RPAREN
    | dist NEQUALS dist
    | NOT dist
    (* Definitely unsupported in distances *)
    | BOOL
    | LSQUAREB RSQUAREB
    | dist CONCAT dist                                     { "Unsupported operation in type distance"
                                                             |> print_error None; Error}

dist_call_args: d=dist COMMA ds=dist_call_args             { d::ds }
              | d=dist                                     { [d] }

dist_hat: l=DIST d=dist     { match d with
                              | VarDist{ var } -> HatVarDist{ var=var; lnum=Some(l); ty=None }
                              | _ -> ("The ^ operator is only allowed on variables"
                                      |> print_error (Some l));
                                     Error}

(* --------------------------------------------------------------------------
 * EXPRESSIONS
 * -------------------------------------------------------------------------- *)
exp: n=INT                                                  { IntExp(n) }
   | n=FLOAT                                                { FloatExp(n) }
   | i=IDENTIFIER                                           { VarExp{ var=i; lnum=None; ty=None } }
   | b=BOOL                                                 { BoolExp(b) }
   | l=EPSILON                                              { EpsilonExp{lnum=Some(l)} }
   | l=EPSILONVAR                                           { EpsilonVarExp{lnum=Some(l)} }
   | i=IDENTIFIER l=LPAREN args=exp_call_args? RPAREN       { CallExp{ lnum=Some(l)
                                                                     ; func=i
                                                                     ; args=nil_if_none args
                                                                     ; ty=None } }
   | e1=exp l1=QMARK e2=exp l2=COLON e3=exp                 { TernaryExp{ cond_exp=e1
                                                                        ; then_lnum=Some(l1)
                                                                        ; then_exp=e2
                                                                        ; else_lnum=Some(l2)
                                                                        ; else_exp=e3
                                                                        ; ty=None }}
   | e1=exp o=op e2=exp                                     { let (lnum, op) = o
                                                              in OpExp{ lnum=Some(lnum)
                                                                      ; left=e1
                                                                      ; right=e2
                                                                      ; op=op
                                                                      ; ty=None } }
   | l=MINUS e=exp %prec UMINUS                             { UMinusExp{ lnum=Some(l)
                                                                       ; exp=e
                                                                       ; ty=None }}
   | e1=exp l=NEQUALS e2=exp                                { NotExp { lnum=Some(l)
                                                                     ; exp=OpExp{ lnum=Some(l)
                                                                                ; left=e1
                                                                                ; right=e2
                                                                                ; op=EqOp
                                                                                ; ty=None } } }
   | l=NOT e=exp                                            { NotExp { lnum=Some(l); exp=e } }
   | l=NIL                                                  { NilExp { lnum=Some(l); ty=None} }
   | e1=exp l=CONCAT e2=exp                                 { ConcatExp{ lnum=Some(l)
                                                                       ; elem=e1
                                                                       ; list=e2
                                                                       ; ty=None } }
   | e1=exp l=LSQUAREB e2=exp RSQUAREB                      { SubExp{ lnum=Some(l)
                                                                    ; list=e1
                                                                    ; idx=e2
                                                                    ; ty=None} }
   | LPAREN e=exp RPAREN                                    { e }
   | l=DIST e=exp                                           { match e with
                                                              | VarExp{ var } -> HatVarExp{ var=var
                                                                                          ; lnum=Some(l)
                                                                                          ; ty=None }
                                                              | _ -> ("The ^ operator is only allowed on variables"
                                                                      |> print_error (Some l)); Error}

exp_call_args: e=exp COMMA es=exp_call_args                 { e::es }
             | e=exp                                        { [e] }

(* --------------------------------------------------------------------------
 * ANNOTATION
 * -------------------------------------------------------------------------- *)
anno_vars: i=IDENTIFIER ix=anno_vars?                     { concat_if_some i ix }

anno_list: anno=anno EOC? annos=anno_list?                { concat_if_some anno annos }

anno: a=av COLON? aexp=anno_exp                           { let (lnum, av') = a
                                                            in Annotation { lnum=Some(lnum); av=av'; aexp=aexp} }
    | a=av COLON? exp=exp                                 { let (lnum, av') = a
                                                            in Annotation { lnum=Some(lnum); av=av'; aexp=Prop(exp)} }

av : lnum=INVARIANT                                       { (lnum, Invariant) }
   | lnum=TERMINATION                                     { (lnum, Termination) }
   | lnum=PRECONDITION                                    { (lnum, Precondition) }
   | lnum=POSTCONDITION                                   { (lnum, Postcondition) }

anno_exp: q=anno_quant vs=anno_vars t=ty_o? a=anno_exp    { Quantifier(q,vs,t,a) }
        | COMMA e=exp                                     { Prop(e) }

anno_quant: FORALL                                        { Forall }
          | EXISTS                                        { Exists }


(* --------------------------------------------------------------------------
 * STATEMENTS
 * -------------------------------------------------------------------------- *)
stmt: (* Conditional statements*)
      l1=IF LPAREN e=exp RPAREN l2=LBRACKET c1=stmt RBRACKET cs=stmt?
        { concat_if_some (IfStmt { cond_lnum=Some(l1)
                                 ; cond_exp=e
                                 ; then_lnum=Some(l2)
                                 ; then_body=c1
                                 ; then_dist_venv=SMap.empty
                                 ; else_lnum=None
                                 ; else_body=[]
                                 ; else_dist_venv=SMap.empty
                                 }) cs }
    | l1=IF LPAREN e=exp RPAREN l2=LBRACKET c1=stmt RBRACKET ELSE l3=LBRACKET c2=stmt RBRACKET cs=stmt?
        { concat_if_some (IfStmt { cond_lnum=Some(l1)
                                 ; cond_exp=e
                                 ; then_lnum=Some(l2)
                                 ; then_body=c1
                                 ; then_dist_venv=SMap.empty
                                 ; else_lnum=Some(l3)
                                 ; else_body=c2
                                 ; else_dist_venv=SMap.empty
                                 }) cs }
      (* Loops *)
    | lnum=WHILE LPAREN e=exp RPAREN a=anno_list? LBRACKET c=stmt RBRACKET cs=stmt?
        { concat_if_some (WhileStmt { lnum=Some(lnum)
                                    ; cond_exp=e
                                    ; annos=nil_if_none a
                                    ; body=c
                                    ; body_dist_venv=SMap.empty
                                    }) cs }
      (* Sequential statements*)
    | c=stmt_simp EOC cx=stmt?
        { concat_if_some c cx }

(* Statements independent of ';' *)
stmt_simp: (* Skip *)
          l=SKIP                                                 { SkipStmt { lnum=Some(l) } }
        (* Declarations *)
        | l=LET m=MUT? i=IDENTIFIER t=ty_o? ASSIGN e=exp         { DeclStmt { lnum=Some(l); ty=t; var=i; exp=e; mut=is_some m } }
        (* Assignment *)
        | i=IDENTIFIER l=ASSIGN e=exp                            { AssignStmt { lnum=Some(l); var=i; exp=e } }
        (* Return *)
        | l=RETURN e=exp                                         { ReturnStmt { lnum=Some(l); exp=e } }


(* --------------------------------------------------------------------------
 * PROGRAM
 * -------------------------------------------------------------------------- *)
prog: al=anno_list?
      name=IDENTIFIER l=LPAREN args=arg_list? RPAREN ret_ty=ty_o?
      LBRACKET c=stmt? RBRACKET
                                                            { Program { lnum=Some(l)
                                                                      ; name=name
                                                                      ; annos=nil_if_none al
                                                                      ; stmts=nil_if_none c
                                                                      ; stmts_dist_venv=SMap.empty
                                                                      ; args=nil_if_none args
                                                                      ; ret_ty=ret_ty } }

arg_list: m=MUT? i=IDENTIFIER t=ty_o?                       { [Arg { var=i; ty=t; mut=is_some m }] }
        | m=MUT? i=IDENTIFIER t=ty_o? COMMA args=arg_list   { (Arg { var=i; ty=t; mut=is_some m })::args }
