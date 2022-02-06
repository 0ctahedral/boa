open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs

(* Runs a program, given as a source string, and compares its output to expected *)
let t (name : string) (program : string) (expected : string) = name>::test_run program name expected;;

(* Runs a program, given as an ANFed expr, and compares its output to expected *)
let ta (name : string) (program : tag expr) (expected : string) = name>::test_run_anf program name expected;;

(* Runs a program, given as a source string, and compares its error to expected *)
let te (name : string) (program : string) (expected_err : string) = name>::test_err program name expected_err;;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf (name : string) (program : 'a expr) (expected : unit expr) = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_expr;;

(* tests tagging *)
let ttag (name : string) (program : 'a expr) (expected : tag expr) = name>::fun _ ->
  assert_equal expected (tag program) ~printer:string_of_expr_tagged;;

let tscope (name : string) (program : string) = name>::fun _ ->
  assert_equal () (check_scope (parse_string name program));;

(* Checks if two strings are equal *)
let teq (name : string) (actual : string) (expected : string) = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let tprog (filename : string) (expected : string) = filename>::test_run_input filename expected;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let teprog (filename : string) (expected : string) = filename>::test_err_input filename expected;;

let forty_one = "41";;

let forty_one_a = (ENumber(41L, ()))

(*let suite =
"suite">:::
 [

  tanf "forty_one_anf"
       (ENumber(41L, ()))
       forty_one_a;

  (* For CS4410 students, with unnecessary let-bindings *)
  tanf "prim1_anf_4410"
       (EPrim1(Sub1, ENumber(55L, ()), ()))
       (ELet(["unary_1", EPrim1(Sub1, ENumber(55L, ()), ()), ()],
             EId("unary_1", ()),
             ()));

  (* For CS6410 students, with optimized let-bindings *)
  tanf "prim1_anf_6410"
       (EPrim1(Sub1, ENumber(55L, ()), ()))
       (EPrim1(Sub1, ENumber(55L, ()), ()));

  ta "forty_one_run_anf" (tag forty_one_a) "41";
 
  t "forty_one" forty_one "41";


  tprog "test1.boa" "3";
      
    (* Some useful if tests to start you off *)

  t "if1" "if 5: 4 else: 2" "4";
  t "if2" "if 0: 4 else: 2" "2";

  ]
;;
*)

let scope_suite =
"scope_suite">:::
[
  tscope "number" "42";
  tscope "simple_let" "let x = 2 in x";
  te "variable" "x" "x not in scope at";
  tscope "prim1" "add1(2)";
  tscope "prim1_2" "sub1(2)";
  tscope "prim2" "2 + 3";
  tscope "let_op" "let x = 2 in 2 + x";
  tscope "let_op2" "let x = 3 in let y = 8 in x + y";
  te "invalid_bind" "let y = x in y" "x not in scope at";
  te "invalid_body" "let x = 3 in y" "y not in scope at";
  tscope "multiple_bind" "let x = 3, y = 4 in x * y";
  tscope "multiple_bind2" "let x = 3, y = 4 in let z = 5 in x + y * z";
  te "invalid_multiple_bind" "let x = 3, y = 4, x = 5 in x - y" "x already bound in this let expression at";
  tscope "shadow" "let x = 3 in let x = 4 in x";
  tscope "if" "let x = if 0: 4 else: 5 in add1(x)";
]
;;

let tag_suite =
"tag_suite">:::
[

  ttag "prim1_tag"
       (EPrim1(Sub1, ENumber(55L, ()), ()))
       (EPrim1(Sub1, ENumber(55L, 1), 0));

  ttag "prim2_tag_simple"
       (EPrim2(Plus, ENumber(42L, ()), ENumber(13L, ()), ()))
       (EPrim2(Plus, ENumber(42L, 1), ENumber(13L, 2), 0));

  ttag "prim2_tag_nested"
       (EPrim2(Plus, EPrim2(Minus, ENumber(42L, ()), EId("x", ()), ()), ENumber(13L, ()), ()))
       (EPrim2(Plus, EPrim2(Minus, ENumber(42L, 2), EId("x", 3), 1), ENumber(13L, 4), 0));

  ttag "let_tag"
        (ELet([
          ("a", EPrim2(Minus, EId("b", ()), EId("c", ()), ()), ()); 
          ("d", EPrim2(Minus, EId("e", ()), EId("f", ()), ()), ()); 
        ], EPrim2(Minus, EId("a", ()), EId("d", ()), ()), ()))
        (ELet([
          ("a", EPrim2(Minus, EId("b", 3), EId("c", 4), 2), 1); 
          ("d", EPrim2(Minus, EId("e", 7), EId("f", 8), 6), 5); 
        ], EPrim2(Minus, EId("a", 10), EId("d", 11), 9), 0)) ;

  ttag "if_tag"
        (EIf(EPrim2(Minus, EId("b", ()), EId("c", ()), ()),
          EPrim2(Minus, EId("e", ()), EId("f", ()), ()),
          ENumber(13L, ()), ()))
        (EIf(EPrim2(Minus, EId("b", 2), EId("c", 3), 1),
          EPrim2(Minus, EId("e", 5), EId("f", 6), 4),
          ENumber(13L, 7), 0)) ;


]
;;

let anf_suite =
"anf_suite">:::
[

  tanf "number_anf"
       (ENumber(55L, ()))
       (ENumber(55L, ()));

  tanf "prim1_anf"
       (EPrim1(Sub1, ENumber(55L, ()), ()))
       (ELet(["$prim1_0", EPrim1(Sub1, ENumber(55L, ()), ()), ()],
             EId("$prim1_0", ()),
             ()));

  tanf "nested_prim1_anf"
       (EPrim1(Sub1, EPrim1(Add1, ENumber(55L, ()), ()), ()))
       (ELet(["$prim1_1", EPrim1(Add1, ENumber(55L, ()), ()), ()],
         ELet(["$prim1_0", EPrim1(Sub1, EId("$prim1_1", ()), ()), ()], EId("$prim1_0", ()), ()),
             ()));

  tanf "prim2_anf"
       (EPrim2(Plus, ENumber(13L, ()), ENumber(55L, ()), ()))
       (ELet([("$prim2_0", EPrim2(Plus, ENumber(13L, ()), ENumber(55L, ()), ()), ())],
          EId("$prim2_0", ()),
          ()));

  tanf "nested_prim1_in_prim2_anf"
       (EPrim2(Plus, ENumber(13L, ()), EPrim1(Add1, ENumber(55L, ()), ()), ()))
       (ELet([("$prim1_2", EPrim1(Add1, ENumber(55L, ()), ()), ())],
          ELet([("$prim2_0", EPrim2(Plus, ENumber(13L, ()), EId("$prim1_2", ()), ()), ())],
            EId("$prim2_0", ()), ()),
        ()));

  tanf "if_anf"
       (EIf(ENumber(0L, ()), ENumber(13L, ()), EPrim1(Add1, ENumber(55L, ()), ()), ()))
       (ELet([("$prim1_3", EPrim1(Add1, ENumber(55L, ()), ()), ())],
         ELet([("$if_0", EIf(ENumber(0L, ()), ENumber(13L, ()), EId("$prim1_3", ()), ()), ())],
            EId("$if_0", ()), ()),
          ()));

  tanf "if_nested_more_anf"
       (EIf(ENumber(0L, ()), EPrim2(Times, ENumber(13L, ()), ENumber(13L, ()), ()), EPrim1(Add1, ENumber(55L, ()), ()), ()))
       (
         ELet([("$prim2_2", EPrim2(Times, ENumber(13L, ()), ENumber(13L, ()), ()), ())],
           ELet([("$prim1_5", EPrim1(Add1, ENumber(55L, ()), ()), ())],
             ELet([("$if_0", EIf(ENumber(0L, ()), EId("$prim2_2", ()), EId("$prim1_5", ()), ()), ())],
                EId("$if_0", ()), ()),
            ()),
          ())
        );

  tanf "let_anf"
  (ELet([("x", EPrim2(Times, ENumber(13L, ()), ENumber(13L, ()), ()), ())],
    EPrim1(Add1, EId("x", ()), ()), ()))

  (
    ELet([("$prim2_2", EPrim2(Times, ENumber(13L, ()), ENumber(13L, ()), ()), ())],
      ELet([("x", EId("$prim2_2", ()), ())],
        ELet([("$prim1_5", EPrim1(Add1, EId("x", ()), ()), ())],
          EId("$prim1_5", ()),
        ()),
      ()),
    ())
          
    );

  tanf "let_anf2"
  (ELet([("x", EPrim2(Times, ENumber(13L, ()), ENumber(13L, ()), ()), ());
          ("y", EPrim2(Times, ENumber(4L, ()), EId("x", ()), ()), ())],
    EPrim1(Add1, EId("x", ()), ()), ()))

  (
    ELet([("$prim2_2", EPrim2(Times, ENumber(13L, ()), ENumber(13L, ()), ()), ())],
      ELet([("x", EId("$prim2_2", ()), ())],
        ELet([("$prim2_6", EPrim2(Times, ENumber(4L, ()), EId("x", ()), ()), ())],
          ELet([("y", EId("$prim2_6", ()), ())],
            ELet([("$prim1_9", EPrim1(Add1, EId("x", ()), ()), ())],
              EId("$prim1_9", ()),
            ()),
          ()),
        ()),
      ()),
    ())
          
    );

]
;;

let () =
  (*run_test_tt_main suite*)
  run_test_tt_main scope_suite;;
  run_test_tt_main tag_suite;;
  run_test_tt_main anf_suite;;
;;
