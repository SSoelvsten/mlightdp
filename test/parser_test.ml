open OUnit2
open Env
open Ast

(* --------------------------------------------------------------------------
 * TEST CASE WRAPPERS
 * -------------------------------------------------------------------------- *)
let test_from_string (parser: (Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a)
                     (input: string)
                     (expected: 'a) =
  let lexbuf = Lexing.from_string input in
  try let result = parser Lexer.tokenize lexbuf in
    (fun test_ctxt -> assert_equal result expected) with
  | Lexer.SyntaxError msg -> assert_failure ("Syntax Error: " ^ msg)
  | Parser.Error -> assert_failure "Parsing Error"

let test_exp (input: string) (expected: (ty_dist option ty option) exp) =
  test_from_string Parser.main_exp input expected

let test_stmt (input: string) (expected: (ty_dist option ty option) stmt list) =
  test_from_string Parser.main_stmt input expected

let test_prog (input: string) (expected: (ty_dist option ty option) prog) =
  test_from_string Parser.main_prog input expected

(* --------------------------------------------------------------------------
 * EXPRESSIONS
 * -------------------------------------------------------------------------- *)

let int_test = test_exp "42" (IntExp(42))
let float_test = test_exp "21.5" (FloatExp(21.5))
let bool_true_test = test_exp "true" (BoolExp(true))
let bool_false_test = test_exp "false" (BoolExp(false))
let epsilon_test = test_exp "epsilon" (EpsilonExp{lnum=Some(1)})
let op_test = test_exp "21 * 2" (OpExp{ lnum=Some(1)
                                      ; left=IntExp(21)
                                      ; right=IntExp(2)
                                      ; op=TimesOp
                                      ; ty=None })

let precedence_test = test_exp "true && 20*2 + 2.0 == answer || epsilon > 0"
    (OpExp{ lnum=Some 1
          ; left=OpExp{ lnum=Some 1
                      ; left=BoolExp true
                      ; right=OpExp{ lnum=Some 1
                                   ; left=OpExp{ lnum=Some 1
                                               ; left=OpExp{ lnum=Some 1
                                                           ; left=IntExp 20
                                                           ; right=IntExp 2
                                                           ; op=TimesOp
                                                           ; ty=None}
                                               ; right=FloatExp 2.0
                                               ; op=PlusOp
                                               ; ty=None}
                                   ; right=VarExp{ var="answer"; lnum=None; ty=None }
                                   ; op=EqOp
                                   ; ty=None}
                      ; op=AndOp
                      ; ty=None}
          ; right=OpExp{ lnum=Some(1)
                       ; left=EpsilonExp{lnum=Some 1}
                       ; right=IntExp 0
                       ; op=GtOp
                       ; ty=None}
          ; op=OrOp
          ; ty=None})

let ternary_precedence_test = test_exp "q + e >= t ? 2 : 0"
    (TernaryExp{ cond_exp=OpExp{ lnum=Some 1
                               ; left=OpExp{ lnum=Some 1
                                           ; left=VarExp{ var="q"; lnum=None; ty=None }
                                           ; right=VarExp{ var="e"; lnum=None; ty=None }
                                           ; op=PlusOp
                                           ; ty=None
                                           }
                               ; right=VarExp{ var="t"; lnum=None; ty=None }
                               ; op=GeOp
                               ; ty=None
                               }
               ; then_lnum=Some 1
               ; then_exp=IntExp 2
               ; else_lnum=Some 1
               ; else_exp=IntExp 0
               ; ty=None
    })

let implies_precedence = test_exp "a && b ==> c ==> d"
    (OpExp{ lnum=Some 1
          ; left=OpExp{ lnum=Some 1
                      ; left=VarExp{var="a"; lnum=None; ty=None}
                      ; right=VarExp{var="b"; lnum=None; ty=None}
                      ; op=AndOp
                      ; ty=None
                      }
          ; right=OpExp{ lnum=Some 1
                       ; left=VarExp{var="c"; lnum=None; ty=None}
                       ; right=VarExp{var="d"; lnum=None; ty=None}
                       ; op=ImpliesOp
                       ; ty=None
                       }
          ; op=ImpliesOp
          ; ty=None
          })

let simple_call_test = test_exp "Dist(i)"
    (CallExp{ lnum=Some(1)
            ; func="Dist"
            ; args=[VarExp{ var="i"; lnum=None; ty=None }]
            ; ty = None
            })

let call_test = test_exp "Lap(2,i+2)"
    (CallExp{ lnum=Some 1
            ; func="Lap"
            ; args=[IntExp 2
                   ; OpExp{ lnum=Some 1
                          ; left=VarExp{ var="i"; lnum=None; ty=None }
                          ; right=IntExp 2
                          ; op=PlusOp; ty=None
                          }]
            ; ty=None })

let subscript_test = test_exp "2.0 + q[i]"
    (OpExp{ lnum=Some 1
          ; left=FloatExp 2.0
          ; right=SubExp{lnum=Some 1
                        ; list=VarExp{ var="q"; lnum=None; ty=None }
                        ; idx=VarExp{ var="i"; lnum=None; ty=None }
                        ; ty=None
                        }
          ; op=PlusOp
          ; ty=None } )

let subscript_assoc_test = test_exp "q[w[i]]"
    (SubExp{ lnum=Some 1
           ; list=VarExp{ var="q"; lnum=None; ty=None }
           ; idx=SubExp{lnum=Some 1
                       ; list=VarExp{ var="w"; lnum=None; ty=None }
                       ; idx=VarExp{ var="i"; lnum=None; ty=None }
                       ; ty=None
                       }
           ; ty=None })

let concat_assoc_test = test_exp "1 :: 2.0 :: 3 :: []"
    (ConcatExp{ lnum=Some 1
              ; elem=IntExp 1
              ; list=ConcatExp{lnum=Some 1
                              ; elem=FloatExp 2.0
                              ; list=ConcatExp{ lnum=Some 1
                                              ; elem=IntExp 3
                                              ; list=NilExp{lnum=Some 1; ty=None }
                                              ; ty=None
                                              }
                              ; ty=None
                              }
              ; ty=None
              })

(* let concat_sub_test = test_exp "(1 :: 2 :: [])[0]" *)

let uminus_precedence_test = test_exp "-q[i]"
    (UMinusExp{ lnum=Some 1
              ; exp=SubExp{ lnum=Some 1
                          ; list=VarExp{ var="q"; lnum=None; ty=None }
                          ; idx=VarExp{ var="i"; lnum=None; ty=None }
                          ; ty=None
                          }
              ; ty=None
              })

let dist_precedence_test = test_exp "^q[i]"
    (SubExp{ lnum=Some 1
           ; list=HatVarExp{ var="q"; lnum=Some 1; ty=None }
           ; idx=VarExp{ var="i"; lnum=None; ty=None }
           ; ty=None
           })


(* --------------------------------------------------------------------------
 * STATEMENTS
 * -------------------------------------------------------------------------- *)

(** Simple stmtands *)
let return_test = test_stmt
    "return 0;"
    [ReturnStmt{lnum=Some 1; exp=IntExp 0}]

let skip_test = test_stmt "skip;"
    [SkipStmt{lnum=Some 1 }]

let assign_test = test_stmt
    "x = 0;"
    [AssignStmt{lnum=Some 1; var="x"; exp=IntExp 0}]

let decl_test_minimal = test_stmt
    "let i = 0;"
    [DeclStmt{lnum=Some 1; ty=None; var="i"; exp=IntExp 0; mut=false}]

let decl_test_ty = test_stmt
    "let i : int = 0;"
    [DeclStmt{ lnum=Some 1
             ; ty=Some(IntTy(None))
             ; var="i"
             ; exp=IntExp 0
             ; mut=false}]

let decl_test_mut = test_stmt
    "let mut i = 0;"
    [DeclStmt{lnum=Some 1; ty=None; var="i"; exp=IntExp 0; mut=true}]

let decl_test_full = test_stmt
    "let mut i : int[*] = 0;"
    [DeclStmt{ lnum=Some 1
             ; ty=Some(IntTy(Some(SigmaDist)))
             ; var="i"
             ; exp=IntExp 0
             ; mut=true}]

(* Should print an error *)
let decl_test_v_eps_in_dist = test_stmt
    "let mut i : int[v_epsilon] = 0;"
    [DeclStmt{ lnum=Some 1
             ; ty=Some(IntTy(Some(Dist(Error))))
             ; var="i"
             ; exp=IntExp 0
             ; mut=true}]

(** Advanced stmtands *)

let if_test = test_stmt
    "if (true) { return 1; }"
    [
      IfStmt{ cond_lnum=Some 1
            ; cond_exp=BoolExp(true)
            ; then_lnum=Some 1
            ; then_body=[ReturnStmt{lnum=Some(1); exp=IntExp(1)}]
            ; then_dist_venv=SMap.empty
            ; else_lnum=None
            ; else_body=[]
            ; else_dist_venv=SMap.empty
            }
    ]

let while_test = test_stmt
    "while(true){ skip; }"
    [WhileStmt { lnum=Some 1
               ; cond_exp=BoolExp(true)
               ; annos=[]
               ; body=[SkipStmt{lnum=Some(1)}]
               ; body_dist_venv=SMap.empty
               }
    ]

let while_test_w_annos = test_stmt
    "while(true)
    invariant: true;
     {
       skip;
     }"
    [WhileStmt { lnum=Some 1
               ; cond_exp=BoolExp(true)
               ; annos=[
                   Annotation{lnum=Some 2
                             ; av=Invariant
                             ; aexp=Prop(BoolExp(true))}
                 ]
               ; body=[SkipStmt {lnum=Some 4}]
               ; body_dist_venv=SMap.empty
               }
    ]

(* --------------------------------------------------------------------------
 * PROGRAMS
 * -------------------------------------------------------------------------- *)
let simple_prog_test = test_prog
    "test_fun() { skip; }"
    (Program{ lnum=Some 1
            ; annos=[]
            ; stmts=[SkipStmt{lnum=Some 1}]
            ; stmts_dist_venv=SMap.empty
            ; name="test_fun"
            ; args=[]
            ; ret_ty=None
            })

let prog_test_w_args = test_prog
    "test_fun(a: bool, b: float[*], mut c: int[2]) { skip; }"
    (Program{ lnum=Some(1)
            ; annos=[]
            ; stmts=[SkipStmt{lnum=Some 1}]
            ; stmts_dist_venv=SMap.empty
            ; name="test_fun"
            ; args=
                [ Arg{ var="a"
                      ; ty=Some BoolTy
                      ; mut=false }
                ; Arg{ var="b"
                      ; ty=Some(FloatTy(Some SigmaDist))
                      ; mut=false }
                ; Arg{ var="c"
                      ; ty=Some(IntTy(Some(Dist(IntDist 2))))
                      ; mut=true }
                ]
            ; ret_ty=None
          }
       )

let prog_test_w_annos = test_prog
    "precondition:  forall i, i < 42;
     postcondition: exists i j : int, true;
     test_fun() { skip; }"
    (Program{ lnum=Some 3
            ; annos=[
                Annotation{ lnum=Some 1
                          ; av=Precondition
                          ; aexp=Quantifier(Forall
                                           , ["i"]
                                           , None
                                           , Prop(OpExp{ lnum=Some 1
                                                       ; left=VarExp{ var="i"; lnum=None; ty=None }
                                                       ; right=IntExp 42
                                                       ; op=LtOp
                                                       ; ty=None
                                                       }
                                                 )
                                           )
                          }
              ; Annotation{ lnum=Some 2
                          ; av=Postcondition
                          ; aexp=Quantifier(Exists
                                           , ["i"; "j"]
                                           , Some(IntTy(None))
                                           , Prop(BoolExp(true))
                                           )
                          }
              ]
            ; stmts=[SkipStmt{lnum=Some 3}]
            ; stmts_dist_venv=SMap.empty
            ; name="test_fun"
            ; args=[]
            ; ret_ty=None } )

let prog_test_w_anno_w_args = test_prog
    "precondition: forall i : float[3] exists j k : bool, true;
     test_fun(q: list(float[*])[0]) { skip; }"
    (Program{ lnum=Some 2
            ; annos=[
                Annotation{ lnum=Some 1
                          ; av=Precondition
                          ; aexp=Quantifier(Forall
                                           , ["i"]
                                           , Some(FloatTy(Some(Dist(IntDist 3))))
                                           , Quantifier ( Exists
                                                        , ["j";"k"]
                                                        , Some(BoolTy)
                                                        , Prop(BoolExp(true))
                                                        )
                                           )
                          }
              ]
            ; stmts=[SkipStmt{lnum=Some 2}]
            ; stmts_dist_venv=SMap.empty
            ; name="test_fun"
            ; args=[Arg{ var="q"
                       ; ty=Some(ListTy(FloatTy(Some(SigmaDist))))
                       ; mut=false
                       } ]
            ; ret_ty=None } )

(* --------------------------------------------------------------------------
 * RUN TESTS
 * -------------------------------------------------------------------------- *)
let () =
  run_test_tt_main (
  "parser_tests" >:::
  [ (* expressions *)
    "int_test" >:: int_test;
    "float_test" >:: float_test;
    "bool_true_test" >:: bool_true_test;
    "bool_false_test" >:: bool_false_test;
    "epsilon_test" >:: epsilon_test;
    "op_test" >:: op_test;
    "precedence_test" >:: precedence_test;
    "implies_precedence" >:: implies_precedence;
    "ternary_precedence_test" >:: ternary_precedence_test;
    "simple_call_test" >:: simple_call_test;
    "call_test" >:: call_test;
    "subscript_test" >:: subscript_test;
    "subscript_assoc_test" >:: subscript_assoc_test;
    "concat_assoc_test" >:: concat_assoc_test;
    "uminus_precedence_test" >:: uminus_precedence_test;
    "dist_precedence_test" >:: dist_precedence_test;
    (* Statements *)
    "return_test" >:: return_test;
    "skip_test" >:: skip_test;
    "assign_test" >:: assign_test;
    "decl_test_minimal" >:: decl_test_minimal;
    "decl_test_ty" >:: decl_test_ty;
    "decl_test_mut" >:: decl_test_mut;
    "decl_test_full" >:: decl_test_full;
    "decl_test_v_eps_in_dist" >:: decl_test_v_eps_in_dist;
    "if_test" >:: if_test;
    "while_test" >:: while_test;
    "while_test_w_annos" >:: while_test_w_annos;
    (* Programs *)
    "simple_prog_test" >:: simple_prog_test;
    "prog_test_w_args" >:: prog_test_w_args;
    "prog_test_w_annos" >:: prog_test_w_annos;
    "prog_test_w_anno_w_args" >:: prog_test_w_anno_w_args
  ])
