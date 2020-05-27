open OUnit2
open Env
open Ast
open Semant
open Exception


(* --------------------------------------------------------------------------
 * TEST CASE WRAPPERS
 * -------------------------------------------------------------------------- *)

let test_from_ast    (result: 'a)
                     (expected: 'a) =
  try (fun test_ctxt -> assert_equal result expected) with
  | Exception.NotImplemented msg -> assert_failure ("Not Implemented: " ^ msg)
  | Exception.DevMessage msg     -> assert_failure ("Developer Message: " ^ msg)
  | Exception.CompilationFail    -> assert_failure "Compilation failed"
  | _                            -> assert_failure "Oh no, I don't know how OUnit even works :("

let test_dist (input: dist) (ctxt: ctxt) (expected: dist) =
  let output = Semant.s_dist input (ctxt |> update_expected_ty (Some (FloatTy None)))
  in test_from_ast output expected

let test_exp (input: ty_from exp) (ctxt: ctxt) (expected: ty_to exp) =
  let output = Semant.s_exp input ctxt
  in test_from_ast output expected

let test_stmts (input: ty_from stmt list) (ctxt: ctxt) (expected: ty_to stmt list) =
  let (output, _) = Semant.s_stmts input ctxt
  in test_from_ast output expected

let test_prog_annos (input: ty_from annotation list) (ctxt: ctxt) (expected: ty_to annotation list) =
  let output = Semant.s_prog_annos input ctxt
  in test_from_ast output expected

let test_while_annos (input: ty_from annotation list) (ctxt: ctxt) (expected: ty_to annotation list) =
  let output = Semant.s_while_annos input ctxt
  in test_from_ast output expected

let test_prog (input: ty_from prog) (expected: ty_to prog) =
  let output = Semant.s_prog input
  in test_from_ast output expected

(* --------------------------------------------------------------------------
 * CONTEXT
 * -------------------------------------------------------------------------- *)
let empty_ctxt = { venv=SMap.empty
                 ; ret_ty=None
                 ; expected_ty=None
                 ; lnum=None
                 ; allow_epsilonvar=false
                 ; allow_hatvar=false
                 }

(* --------------------------------------------------------------------------
 * DISTANCES
 * -------------------------------------------------------------------------- *)
let type_cast_int_var = test_dist (VarDist { var="t"; lnum=None; ty=None})
    (empty_ctxt |> update_venv "t" { ty=IntTy(None); mut=false })
    (TypeCastDist{ dist=VarDist{ var="t"
                               ; lnum=None
                               ; ty=Some(IntTy ())}
                 ; to_ty=FloatTy () })

let dist_int_expected = test_dist (SubDist { lnum=Some 11
                                           ; list=VarDist { var="l"; lnum=None; ty=None}
                                           ; idx=VarDist { var="i"; lnum=None; ty=None}
                                           ; ty=None})
    (empty_ctxt |> update_venv "i" { ty=FloatTy(None); mut=false }
                |> update_venv "l" { ty=ListTy(IntTy None); mut=false })
    Error

let dist_int_index_1 = test_dist
    (SubDist { lnum=Some 11
             ; list=VarDist { var="l"; lnum=None; ty=None}
             ; idx=IntDist 2
             ; ty=None})
    (empty_ctxt |> update_venv "i" { ty=IntTy(None); mut=false }
                |> update_venv "l" { ty=ListTy(FloatTy None); mut=false })
    (SubDist { lnum=Some 11
             ; list=VarDist { var="l"; lnum=Some 11; ty=Some(ListTy(FloatTy ()))}
             ; idx=IntDist 2
             ; ty=Some(FloatTy ())})

let dist_int_index_2 = test_dist
    (SubDist { lnum=Some 11
             ; list=VarDist { var="l"; lnum=None; ty=None}
             ; idx=OpDist { lnum=None
                          ; left=IntDist 3
                          ; right=IntDist 4
                          ; op=PlusOp
                          ; ty=None
                          }
             ; ty=None})
    (empty_ctxt |> update_venv "l" { ty=ListTy(FloatTy None); mut=false })
    (SubDist { lnum=Some 11
             ; list=VarDist { var="l"; lnum=Some 11; ty=Some(ListTy(FloatTy ()))}
             ; idx=OpDist { lnum=None
                          ; left=IntDist 3
                          ; right=IntDist 4
                          ; op=PlusOp
                          ; ty=Some(IntTy ())
                          }
             ; ty=Some(FloatTy ())})


(* --------------------------------------------------------------------------
 * EXPRESSIONS
 * -------------------------------------------------------------------------- *)
let int_test = test_exp (IntExp 42) empty_ctxt (IntExp 42)
let float_test = test_exp (FloatExp 42.0) empty_ctxt (FloatExp 42.0)

let epsilon_test = test_exp (EpsilonExp{lnum=None}) empty_ctxt (EpsilonExp{lnum=None})

(* Prints: "The privacy leakage variable 'v_epsilon' may only be used in invariants" *)
let epsilon_var_false_test = test_exp (EpsilonVarExp{lnum=None}) empty_ctxt Error
let epsilon_var_true_test =
  let ctxt = empty_ctxt |> update_allowed_special_vars true false
  in test_exp (EpsilonVarExp{lnum=None}) ctxt (EpsilonVarExp{lnum=None})

let bool_test = test_exp (BoolExp true) empty_ctxt (BoolExp true)

let var_test =
  let ctxt = empty_ctxt
             |> update_venv "hello_world" { ty=IntTy(Some(Dist(FloatDist(2.0))))
                                          ; mut=false }
  in test_exp (VarExp{var="hello_world"; lnum=None; ty=None})
              ctxt
              (VarExp{var="hello_world"; lnum=None; ty=IntTy(None)})

let hatvar_test_float =
  let ctxt = empty_ctxt
             |> update_venv "lucky" { ty=FloatTy None
                                    ; mut=false }
             |> update_allowed_special_vars false true
  in test_exp (HatVarExp{var="lucky"; lnum=None; ty=None})
              ctxt
              (HatVarExp{var="lucky"; lnum=None; ty=FloatTy None})

let hatvar_list_test =
  let ctxt = empty_ctxt
             |> update_venv "lucky" { ty=ListTy(FloatTy None); mut=false }
             |> update_allowed_special_vars false true
  in test_exp (HatVarExp{var="lucky"; lnum=None; ty=None})
    ctxt
    (HatVarExp{var="lucky"; lnum=None; ty=ListTy(FloatTy None)})

(* Prints: "The distance variable '^lucky' is only allowed to be referenced within annotations." *)
let hatvar_test_not_inanno =
  let ctxt = empty_ctxt
             |> update_venv "lucky" { ty=FloatTy None
                                    ; mut=false }
             |> update_allowed_special_vars false false
  in test_exp (HatVarExp{var="lucky"; lnum=None; ty=None}) ctxt Error

(* Prints: "Cannot hat 'lucky' of type 'int'" *)
let hatvar_int_test =
  let ctxt = empty_ctxt
             |> update_venv "lucky" { ty=IntTy(Some SigmaDist); mut=false }
             |> update_allowed_special_vars false true
  in test_exp (HatVarExp{ var="lucky"; lnum=None; ty=None }) ctxt Error

(* Prints: "Cannot hat 'lucky' of type 'bool'" *)
let hatvar_bool_test =
  let ctxt = empty_ctxt
             |> update_venv "lucky" { ty=BoolTy; mut=false }
             |> update_allowed_special_vars false true
  in test_exp (HatVarExp{ var="lucky"; lnum=None; ty=None }) ctxt Error

let bool_op_test = test_exp (OpExp{ lnum=None
                                  ; left=BoolExp true
                                  ; right=BoolExp false
                                  ; op=AndOp
                                  ; ty=None })
                            empty_ctxt
                            (OpExp{ lnum=None
                                  ; left=BoolExp true
                                  ; right=BoolExp false
                                  ; op=AndOp
                                  ; ty=BoolTy })

let int_to_float_op_test = test_exp
    (OpExp{ lnum=None
          ; left=IntExp 2
          ; right=FloatExp 2.3
          ; op=PlusOp
          ; ty=None })
    empty_ctxt
    (OpExp{ lnum=None
          ; left=TypeCastExp{ lnum=None; exp=IntExp 2; to_ty=FloatTy () }
          ; right=FloatExp 2.3
          ; op=PlusOp
          ; ty=FloatTy None })

let float_op_test = test_exp (OpExp{ lnum=None
                                   ; left=FloatExp 2.0
                                   ; right=FloatExp 2.3
                                   ; op=PlusOp
                                   ; ty=None })
                            empty_ctxt
                            (OpExp{ lnum=None
                                   ; left=FloatExp 2.0
                                   ; right=FloatExp 2.3
                                   ; op=PlusOp
                                   ; ty=FloatTy None})

let int_op_test = test_exp (OpExp{ lnum=None
                                 ; left=IntExp 40
                                 ; right=IntExp 2
                                 ; op=PlusOp
                                 ; ty=None })
                         empty_ctxt
                         (OpExp{ lnum=None
                               ; left=IntExp 40
                               ; right=IntExp 2
                               ; op=PlusOp
                               ; ty=IntTy None})

let comp_op_test = test_exp (OpExp{ lnum=None
                                  ; left=FloatExp 2.0
                                  ; right=FloatExp 2.3
                                  ; op=GeOp
                                  ; ty=None })
                            empty_ctxt
                            (OpExp{ lnum=None
                                  ; left=FloatExp 2.0
                                  ; right=FloatExp 2.3
                                  ; op=GeOp
                                  ; ty=BoolTy })

let comp_op_test_type_cast = test_exp
    (OpExp{ lnum=None
          ; left=OpExp{ lnum=None
                      ; left=IntExp 2
                      ; right=FloatExp 2.3
                      ; op=GeOp
                      ; ty=None
                      }
          ; right=OpExp{ lnum=None
                       ; left=IntExp 2
                       ; right=FloatExp 2.3
                       ; op=GeOp
                       ; ty=None
                       }
          ; op=AndOp
          ; ty=None
          })
    empty_ctxt
    (OpExp{ lnum=None
          ; left=OpExp{ lnum=None
                      ; left=TypeCastExp{ lnum=None
                                        ; to_ty=FloatTy ()
                                        ; exp=IntExp 2
                                        }
                      ; right=FloatExp 2.3
                      ; op=GeOp
                      ; ty=BoolTy
                      }
          ; right=OpExp{ lnum=None
                       ; left=TypeCastExp{ lnum=None
                                         ; to_ty=FloatTy ()
                                         ; exp=IntExp 2
                                         }
                       ; right=FloatExp 2.3
                       ; op=GeOp
                       ; ty=BoolTy
                       }
          ; op=AndOp
          ; ty=BoolTy
          })




let uminus_int_test = test_exp (UMinusExp{ lnum=Some 42
                                         ; exp=IntExp 2
                                         ; ty=None })
    empty_ctxt
    (UMinusExp{ lnum=Some 42
              ; exp=IntExp 2
              ; ty=IntTy None
              })

let uminus_float_test = test_exp (UMinusExp{ lnum=Some 42
                                           ; exp=FloatExp 2.0
                                           ; ty=None })
    empty_ctxt
    (UMinusExp{ lnum=Some 42
              ; exp=FloatExp 2.0
              ; ty=FloatTy None })

(* Prints: "?" *)
let uminus_bool_test = test_exp (UMinusExp{ lnum=Some 42
                                          ; exp=BoolExp true
                                          ; ty=None
                                          })
    empty_ctxt
    Error

(* Prints: "Error: Operator and operand type mismatch" *)
let mismatch_op_test_1 = test_exp (OpExp{ lnum=Some 42
                                        ; left=FloatExp 2.0
                                        ; right=BoolExp true
                                        ; op=GeOp
                                        ; ty=None
                                        })
    empty_ctxt
    Error

(* Prints: "?" *)
let mismatch_op_test_2 = test_exp (OpExp{ lnum=Some 42
                                        ; left=IntExp 42
                                        ; right=BoolExp false
                                        ; op=AndOp
                                        ; ty=None
                                        })
    empty_ctxt
    Error

let bad_modulo_op_test = test_exp (OpExp{ lnum=Some 42
                                        ; left=FloatExp 4.2
                                        ; right=IntExp 7
                                        ; op=ModuloOp
                                        ; ty=None
                                        })
    empty_ctxt
    Error

let not_test = test_exp
    (NotExp{ lnum=None; exp=BoolExp true})
    empty_ctxt
    (NotExp{ lnum=None; exp=BoolExp true})

let not_int_test = test_exp
    (NotExp{ lnum=None; exp=IntExp 42})
    empty_ctxt
    Error

let ternary_test = test_exp (TernaryExp { cond_exp=BoolExp true
                                        ; then_lnum=None
                                        ; then_exp=IntExp 2
                                        ; else_lnum=None
                                        ; else_exp=IntExp 0
                                        ; ty=None
                                        })
    empty_ctxt
    (TernaryExp { cond_exp=BoolExp true
                ; then_lnum=None
                ; then_exp=IntExp 2
                ; else_lnum=None
                ; else_exp=IntExp 0
                ; ty=IntTy None
                })

let ternary_mismatch_test = test_exp (TernaryExp { cond_exp=BoolExp true
                                                 ; then_lnum=None
                                                 ; then_exp=IntExp 2
                                                 ; else_lnum=None
                                                 ; else_exp=FloatExp 0.0
                                                 ; ty=None
                                                 })
    empty_ctxt
    Error


let concat_test =
  let ctxt = empty_ctxt
             |> update_venv "numbers"
               { ty=ListTy(FloatTy None); mut=false }
  in test_exp (ConcatExp{ lnum=None
                        ; elem=FloatExp 3.0
                        ; list=VarExp{ var="numbers"; lnum=None; ty=None }
                        ; ty=None
                        })
              ctxt
              (ConcatExp{ lnum=None
                        ; elem=FloatExp 3.0
                        ; list=VarExp{ var="numbers"; lnum=None; ty=ListTy(FloatTy None) }
                        ; ty=ListTy(FloatTy(None)) })

(* Prints: "Error: Element type and list type does not match" *)
let concat_error_test =
  let ctxt = empty_ctxt
             |> update_venv "numbers"
               { ty=ListTy(FloatTy None); mut=false }
  in test_exp ( ConcatExp{ lnum=None
                         ; elem=IntExp 42
                         ; list=VarExp{ var="numbers"; lnum=None; ty=None }
                         ; ty=None })
    ctxt
    Error

let sub_test =
  let ctxt = empty_ctxt
             |> update_venv "numbers"
               { ty=ListTy(FloatTy(Some(Dist(FloatDist 42.0))))
               ; mut=false }
  in test_exp ( SubExp{ lnum=None
                      ; list=VarExp{ var="numbers"; lnum=None; ty=None}
                      ; idx=IntExp 1
                      ; ty=None })
    ctxt
    (SubExp{ lnum=None
           ; list=VarExp{ var="numbers"; lnum=None; ty=ListTy(FloatTy(None))}
           ; idx=IntExp 1
           ; ty=FloatTy None })

(* Prints: "?" *)
let sub_non_int_idx_test =
  let ctxt = empty_ctxt |> update_venv "l"
               { ty=ListTy(FloatTy None)
               ; mut=false }
  in test_exp (SubExp{ lnum=None
                     ; list=VarExp{ var="l"; lnum=None; ty=None}
                     ; idx=FloatExp 1.0
                     ; ty=None })
    ctxt
    Error

let sub_nonlist_test = test_exp (SubExp{ lnum=None
                                       ; list=FloatExp 0.0
                                       ; idx=IntExp 1
                                       ; ty=None })
    empty_ctxt
    Error

(* --------------------------------------------------------------------------
 * STATEMENTS
 * -------------------------------------------------------------------------- *)
let skip_test = test_stmts [SkipStmt{lnum=None}] empty_ctxt [SkipStmt{lnum=None}]

let assign_test =
  let ctxt = empty_ctxt |> update_venv "b" {ty=FloatTy None; mut=true}
  in test_stmts [(AssignStmt{ lnum=None
                            ; var="b"
                            ; exp=FloatExp 2.2
                            })]
    ctxt
    [(AssignStmt{ lnum=None
                ; var="b"
                ; exp=FloatExp 2.2
                })]

(* Should print error *)
let undefined_var_test =
  test_stmts [(AssignStmt{ lnum=None
                         ; var="Yorkshire"
                         ; exp=FloatExp 2.2
                         })]
    empty_ctxt
    [(Error)]

let decl_test =
  test_stmts [(DeclStmt{ lnum=None
                       ; ty=Some(FloatTy None)
                       ; var="number"
                       ; exp=FloatExp 42.0
                       ; mut=true
                       })]
    empty_ctxt
    [(DeclStmt{ lnum=None
              ; ty=FloatTy None
              ; var="number"
              ; exp=FloatExp 42.0
              ; mut=true
              })]

let decl_nil_test_1 =
  test_stmts [(DeclStmt{ lnum=None
                       ; ty=Some(ListTy(IntTy None))
                       ; var="nil"
                       ; exp=NilExp{lnum=None; ty=None}
                       ; mut=false
                       })]
    empty_ctxt
    [(DeclStmt{ lnum=None
              ; ty=ListTy(IntTy None)
              ; var="nil"
              ; exp=NilExp{lnum=None; ty=ListTy(IntTy None) }
              ; mut=false
              })]

let decl_nil_test_2 =
  test_stmts [(DeclStmt{ lnum=None
                       ; ty=None
                       ; var="nil"
                       ; exp=NilExp{lnum=None; ty=None }
                       ; mut=false
                       })]
    empty_ctxt
    [Error]


let decl_and_assign =
  test_stmts [(DeclStmt{ lnum=None
                       ; ty=Some(FloatTy None)
                       ; var="number"
                       ; exp=FloatExp 42.0
                       ; mut=true
                       })
             ;(AssignStmt{ lnum=None
                         ; var="number"
                         ; exp=FloatExp 2.2
                         })]
    empty_ctxt
    [(DeclStmt{ lnum=None
              ; ty=FloatTy None
              ; var="number"
              ; exp=FloatExp 42.0
              ; mut=true
              })
    ;(AssignStmt{ lnum=None
                ; var="number"
                ; exp=FloatExp 2.2
                })]

let decl_infer_and_assign =
  test_stmts [(DeclStmt{ lnum=None
                       ; ty=None
                       ; var="number"
                       ; exp=IntExp 42
                       ; mut=true
                       })
             ;(AssignStmt{ lnum=None
                         ; var="number"
                         ; exp=IntExp 2
                         })]
    empty_ctxt
    [(DeclStmt{ lnum=None
              ; ty=IntTy None
              ; var="number"
              ; exp=IntExp 42
              ; mut=true
              })
    ;(AssignStmt{ lnum=None
                ; var="number"
                ; exp=IntExp 2
                })]

(* Should print error *)
let no_mut_test =
  test_stmts [DeclStmt{ lnum=None
                      ; ty=Some(FloatTy None)
                      ; var="the_number"
                      ; exp=FloatExp 42.0
                      ; mut=false
                      }
             ; AssignStmt{ lnum=None
                         ; var="the_number"
                         ; exp=FloatExp 2.2
                         }]
    empty_ctxt
    [(Error)]

let simple_return_test = test_stmts
    [ReturnStmt { lnum=Some 1
                ; exp=FloatExp 1.0
                }]
    empty_ctxt
    [ReturnStmt { lnum=Some 1
                ; exp=FloatExp 1.0
                }]

(* Should print error *)
let return_type_error_test = test_stmts
    [ ReturnStmt { lnum=Some 1
                 ; exp=FloatExp 1.0 }
    ; ReturnStmt { lnum=Some 2
                 ; exp=BoolExp false
                 }]
    empty_ctxt
    [Error]

let if_test = test_stmts
    (* "if (true) { return 1; }" *)
    [
      IfStmt{ cond_lnum=Some 1
            ; cond_exp=BoolExp(true)
            ; then_lnum=Some 1
            ; then_body=[ReturnStmt{lnum=Some 1; exp=FloatExp 1.0 }]
            ; then_dist_venv=SMap.empty
            ; else_lnum=None
            ; else_body=[]
            ; else_dist_venv=SMap.empty
            }
    ]
    empty_ctxt
    [
      IfStmt{ cond_lnum=Some 1
            ; cond_exp=BoolExp(true)
            ; then_lnum=Some 1
            ; then_body=[ReturnStmt{lnum=Some 1; exp=FloatExp 1.0 }]
            ; then_dist_venv=SMap.empty
            ; else_lnum=None
            ; else_body=[]
            ; else_dist_venv=SMap.empty
            }
    ]

let if_scoping_test = test_stmts
    (* "if (true) { return 1; }" *)
    [
      IfStmt{ cond_lnum=Some 1
            ; cond_exp=BoolExp(true)
            ; then_lnum=Some 1
            ; then_body=[
                DeclStmt{ lnum=None
                        ; ty=Some BoolTy
                        ; var="v"
                        ; exp=BoolExp true
                        ; mut=false
                        }
              ]
            ; then_dist_venv=SMap.empty
            ; else_lnum=None
            ; else_body=[]
            ; else_dist_venv=SMap.empty
            }
    ; DeclStmt{ lnum=None
              ; ty=Some(FloatTy None)
              ; var="v"
              ; exp=FloatExp 42.0
              ; mut=false
              }
    ]
    empty_ctxt
    [Error]


 let while_test = test_stmts
    (* "while(true){ skip; }" *)
    [WhileStmt { lnum=Some 1
               ; cond_exp=BoolExp true
               ; annos=[]
               ; body=[SkipStmt{lnum=Some 1}]
               ; body_dist_venv=SMap.empty
               }
    ]
    empty_ctxt
    [WhileStmt { lnum=Some 1
               ; cond_exp=BoolExp true
               ; annos=[]
               ; body=[SkipStmt{lnum=Some 1}]
               ; body_dist_venv=SMap.empty
               }
    ]

let while_scoping_test = test_stmts
    [ WhileStmt { lnum=Some 1
                ; cond_exp=BoolExp true
                ; annos=[]
                ; body=[
                    DeclStmt{ lnum=None
                            ; ty=Some BoolTy
                            ; var="v"
                            ; exp=BoolExp true
                            ; mut=false
                            }
                  ]
                ; body_dist_venv=SMap.empty
                }
    ; DeclStmt{ lnum=None
              ; ty=Some(FloatTy None)
              ; var="v"
              ; exp=FloatExp 42.0
              ; mut=false
              }
    ]
    empty_ctxt
    [Error]

let while_test_w_annos = test_stmts
    (* "while(true)
    invariant: true;
     {
       skip;
     }" *)
    [WhileStmt { lnum=Some 1
               ; cond_exp=BoolExp true
               ; annos=[
                   Annotation{lnum=Some 2; av=Invariant; aexp=Prop(BoolExp true)}
                 ]
               ; body=[SkipStmt {lnum=Some 4}]
               ; body_dist_venv=SMap.empty
               }
    ]
    empty_ctxt
    [WhileStmt { lnum=Some 1
               ; cond_exp=BoolExp true
               ; annos=[
                   Annotation{lnum=Some 2; av=Invariant; aexp=Prop(BoolExp true)}
                 ]
               ; body=[SkipStmt {lnum=Some 4}]
               ; body_dist_venv=SMap.empty
               }
    ]

(* --------------------------------------------------------------------------
 * ANNOTATIONS
 * -------------------------------------------------------------------------- *)

let epsilon_var_in_test = test_while_annos
    [Annotation{lnum=Some 2
               ; av=Invariant
               ; aexp=Prop(OpExp{ left=EpsilonVarExp{lnum=Some 2}
                                ; right=FloatExp 1.0
                                ; op=LeOp
                                ; ty=None
                                ; lnum=Some 3
                                })}]
    empty_ctxt
    [Annotation{lnum=Some 2
               ; av=Invariant
               ; aexp=Prop(OpExp{ left=EpsilonVarExp{lnum=Some 2}
                                ; right=FloatExp 1.0
                                ; op=LeOp
                                ; ty=BoolTy
                                ; lnum=Some 3
                                })}]

let while_annos_test = test_while_annos
    [Annotation{lnum=Some 2; av=Invariant; aexp=Prop(BoolExp true)}]
    empty_ctxt
    [Annotation{lnum=Some 2; av=Invariant; aexp=Prop(BoolExp true)}]

let while_annos_termination_test1 = test_while_annos
    [Annotation{lnum=Some 2; av=Termination; aexp=Prop(IntExp 0)}]
    empty_ctxt
    [Annotation{lnum=Some 2; av=Termination; aexp=Prop(IntExp 0)}]

let while_annos_termination_test2 = test_while_annos
    [Annotation{lnum=Some 2; av=Termination; aexp=Prop(BoolExp false)}]
    empty_ctxt
    [Error]

(* Prints: Illegal annotations: precondition: true *)
let while_annos_error_test_1 = test_while_annos
    [ Annotation{lnum=Some 2; av=Invariant; aexp=Prop(BoolExp true)}
    ; Annotation{lnum=Some 3; av=Precondition; aexp=Prop(BoolExp true)}
    ; Annotation{lnum=Some 4; av=Termination; aexp=Prop(IntExp 2)} ]
    empty_ctxt
    [Error]

(* Prints two messages: "Proposition 'i' in annotation has type 'int',
 * but only propositions of type 'bool' is allowed"
 * where i in {1,2}  *)
let while_annos_error_test_2 = test_while_annos
    [ Annotation{lnum=Some 2; av=Invariant; aexp=Prop(IntExp 1)}
    ; Annotation{lnum=Some 3; av=Invariant; aexp=Prop(IntExp 2)} ]
    empty_ctxt
    [Error]

let prog_anno_test = test_prog_annos
    [Annotation{ lnum=Some 1
                          ; av=Precondition
                          ; aexp=Quantifier(Forall
                                           , ["i"]
                                           , Some(IntTy None)
                                           , Prop(OpExp{ lnum=Some 1
                                                       ; left=VarExp{ var="i"; lnum=None; ty=None }
                                                       ; right=IntExp 42
                                                       ; op=LtOp
                                                       ; ty=None
                                                       }
                                                 )
                                           )
                   }]
      empty_ctxt
      [Annotation{ lnum=Some 1
                          ; av=Precondition
                          ; aexp=Quantifier(Forall
                                           , ["i"]
                                           , IntTy None
                                           , Prop(OpExp{ lnum=Some 1
                                                       ; left=VarExp{ var="i"
                                                                    ; lnum=Some 1
                                                                    ; ty=IntTy None }
                                                       ; right=IntExp 42
                                                       ; op=LtOp
                                                       ; ty=BoolTy
                                                       }
                                                 )
                                           )
                   }]

(* Prints Undefined variable 'j' *)
let prog_anno_error_test = test_prog_annos
    [Annotation{ lnum=Some 1
                          ; av=Precondition
                          ; aexp=Quantifier(Forall
                                           , ["i"]
                                           , Some(IntTy None)
                                           , Prop(OpExp{ lnum=Some 1
                                                       ; left=VarExp{ var="j"; lnum=None; ty=None }
                                                       ; right=IntExp 42
                                                       ; op=LtOp
                                                       ; ty=None
                                                       }
                                                 )
                                           )
                   }]
      empty_ctxt
      [Error]

(* --------------------------------------------------------------------------
 * PROGRAMS
 * -------------------------------------------------------------------------- *)

let simple_prog_test = test_prog
    (* "test_fun() { return 0; }" *)
    (Program{
          lnum=Some(1)
        ; annos=[]
        ; stmts=[ReturnStmt{lnum=Some(1); exp=IntExp 0 }]
        ; stmts_dist_venv=SMap.empty
        ; name="test_fun"
        ; args=[]
        ; ret_ty=None })
    (Program{
          lnum=Some 1
        ; annos=[]
        ; stmts=[ReturnStmt{lnum=Some(1); exp=IntExp 0 }]
        ; stmts_dist_venv=SMap.empty
        ; name="test_fun"
        ; args=[]
        ; ret_ty=IntTy None })

let prog_test_w_annos = test_prog
(*  "precondition:  forall i, i < 42;
     test_fun() { return 0; }" *)
    (Program{ lnum=Some 3
            ; annos=[
                Annotation{ lnum=Some 1
                          ; av=Precondition
                          ; aexp=Quantifier(Forall
                                           , ["i"]
                                           , Some(IntTy None)
                                           , Prop(OpExp{ lnum=Some 1
                                                       ; left=VarExp{ var="i"; lnum=None; ty=None }
                                                       ; right=IntExp 42
                                                       ; op=LtOp
                                                       ; ty=None
                                                       }
                                                 )
                                           )
                   }]
            ; stmts=[ReturnStmt{lnum=Some 1; exp=FloatExp 0.0 }]
            ; stmts_dist_venv=SMap.empty
            ; name="test_fun"
            ; args=[]
            ; ret_ty=Some(FloatTy None) } )
    (Program{ lnum=Some 3
            ; annos=[
                Annotation{ lnum=Some 1
                          ; av=Precondition
                          ; aexp=Quantifier(Forall
                                           , ["i"]
                                           , IntTy None
                                           , Prop(OpExp{ lnum=Some 1
                                                       ; left=VarExp{ var="i"
                                                                    ; lnum=Some 1
                                                                    ; ty=IntTy None }
                                                       ; right=IntExp 42
                                                       ; op=LtOp
                                                       ; ty=BoolTy
                                                       }
                                                 )
                                           )
                   }]
            ; stmts=[ReturnStmt{lnum=Some 1; exp=FloatExp 0.0 }]
            ; stmts_dist_venv=SMap.empty
            ; name="test_fun"
            ; args=[]
            ; ret_ty=FloatTy None })

(* --------------------------------------------------------------------------
 * RUN TESTS
 * -------------------------------------------------------------------------- *)
let () =
  run_test_tt_main (
  "semantic_tests" >:::
  [ (* distances *)
    "type_cast_int_var" >:: type_cast_int_var;
    "dist_int_expected" >:: dist_int_expected;
    "dist_int_index_1" >:: dist_int_index_1;
    "dist_int_index_2" >:: dist_int_index_2;
    (* expressions *)
    "int_test" >:: int_test;
    "float_test" >:: float_test;
    "epsilon_test" >:: epsilon_test;
    "epsilon_var_false_test" >:: epsilon_var_false_test;
    "epsilon_var_true_test" >:: epsilon_var_true_test;
    "bool_test" >:: bool_test;
    "var_test" >:: var_test;
    "hatvar_test_float" >:: hatvar_test_float;
    "hatvar_list_test" >:: hatvar_list_test;
    "hatvar_test_not_inanno" >:: hatvar_test_not_inanno;
    "hatvar_int_test" >:: hatvar_int_test;
    "hatvar_bool_test" >:: hatvar_bool_test;
    "uminus_int_test" >:: uminus_int_test;
    "uminus_float_test" >:: uminus_float_test;
    "uminus_bool_test" >:: uminus_bool_test;
    "bool_op_test" >:: bool_op_test;
    "int_to_float_op_test" >:: int_to_float_op_test;
    "float_op_test" >:: float_op_test;
    "int_op_test" >:: int_op_test;
    "comp_op_test" >:: comp_op_test;
    "comp_op_test_type_cast" >:: comp_op_test_type_cast;
    "mismatch_op_test_1" >:: mismatch_op_test_1;
    "mismatch_op_test_2" >:: mismatch_op_test_2;
    "bad_modulo_op_test" >:: bad_modulo_op_test;
    "not_test" >:: not_test;
    "not_int_test" >:: not_int_test;
    "ternary_test" >:: ternary_test;
    "ternary_mismatch_test" >:: ternary_mismatch_test;
    "concat_test" >:: concat_test;
    "concat_error_test" >:: concat_error_test;
    "sub_test" >:: sub_test;
    "sub_non_int_idx_test" >:: sub_non_int_idx_test;
    "sub_nonlist_test" >:: sub_nonlist_test;
    (* Statements *)
    "skip_test" >:: skip_test;
    "assign_test" >:: assign_test;
    "undefined_var_test" >:: undefined_var_test;
    "decl_test" >:: decl_test;
    "decl_nil_test_1" >:: decl_nil_test_1;
    "decl_nil_test_2" >:: decl_nil_test_2;
    "decl_and_assign" >:: decl_and_assign;
    "no_mut_test" >:: no_mut_test;
    "decl_infer_and_assign" >:: decl_infer_and_assign;
    "simple_return_test" >:: simple_return_test;
    "return_type_error_test" >:: return_type_error_test;
    "if_test" >:: if_test;
    "if_scoping_test" >:: if_scoping_test;
    "while_test" >:: while_test;
    "while_scoping_test" >:: while_scoping_test;
    "while_test_w_annos" >:: while_test_w_annos;
    (* Annotations *)
    "epsilon_var_in_test" >:: epsilon_var_in_test;
    "while_annos_test" >:: while_annos_test;
    "while_annos_termination_test1" >:: while_annos_termination_test1;
    "while_annos_termination_test2" >:: while_annos_termination_test2;
    "while_annos_error_test_1" >:: while_annos_error_test_1;
    "while_annos_error_test_2" >:: while_annos_error_test_2;
    "prog_anno_test" >:: prog_anno_test;
    "prog_anno_error_test" >:: prog_anno_error_test;
    (* Programs *)
    "simple_prog_test" >:: simple_prog_test;
    "prog_test_w_annos" >:: prog_test_w_annos
  ])
