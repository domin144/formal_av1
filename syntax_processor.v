Require Import List ZArith String.
Import ListNotations.

Require Import formal_av1.basic_types.
Require Import formal_av1.pseudocodes.
Require Import formal_av1.parser.
Require Import formal_av1.state.

Module syntax_processor.

Definition definitionsE :=
  (map Parser.parse_pseudocode all_pseudocodes).

Theorem all_definitions_parsed :
  forallb
    (
      fun x => match x with
      | Parser.SomeE (_, []) => true
      | _ => false
      end)
    definitionsE = true.
Proof. reflexivity. Qed.

Definition definitions : list declaration :=
  List.concat
    (
      map
        (
          fun x => match x with
          | Parser.SomeE (x, []) => x
          | _ => []
          end)
        definitionsE).

Reserved Notation "e '//' st '\\' st' \\ x" (at level 50, left associativity).
Reserved Notation "s '/' st '\\' st'" (at level 40, st at level 39).

Inductive expr_result : Type :=
  | er_value : Z -> expr_result
  | er_reference : reference -> expr_result.

Definition binary_negation (x : Z) : Z := -x - 1.

Inductive eval_op1_no_side_effect : any_operator -> Z -> Z -> Prop :=
  | eval_op1_minus_unary :
    forall x,
      eval_op1_no_side_effect (ano_ao ao_minus_unary) x (-x)
  | eval_op1_lo_not :
    forall x,
      eval_op1_no_side_effect (ano_lo lo_not) x (match x with | 0%Z => 1%Z | _ => 0%Z end)
  | eval_op1_bo_neg :
    forall x,
      eval_op1_no_side_effect (ano_bo bo_neg) x (binary_negation x).

(* TODO: bitwise operators *)
Inductive eval_op2_no_side_effect : any_operator -> Z -> Z -> Z -> Prop :=
  | eval_op2_plus :
    forall x0 x1,
      eval_op2_no_side_effect (ano_ao ao_plus) x0 x1 (x0 + x1)
  | eval_op2_minus :
    forall x0 x1,
      eval_op2_no_side_effect (ano_ao ao_minus) x0 x1 (x0 - x1)
  | eval_op2_mult :
    forall x0 x1,
      eval_op2_no_side_effect (ano_ao ao_mult) x0 x1 (x0 * x1)
  | eval_op2_div :
    forall x0 x1,
      x1 <> 0%Z ->
        eval_op2_no_side_effect (ano_ao ao_div) x0 x1 (Z.quot x0 x1)
  | eval_op2_mod :
    forall x0 x1,
      (x0 >= 0)%Z ->
        (x1 > 0)%Z ->
          eval_op2_no_side_effect (ano_ao ao_mod) x0 x1 (Z.rem x0 x1)
  | eval_op2_and :
    forall x0 x1,
      eval_op2_no_side_effect
        (ano_lo lo_and)
        x0
        x1
        (match x0, x1 with | 0%Z, _ => 0%Z | _, 0%Z => 0%Z | _, _ => 1%Z end)
  | eval_op2_or :
    forall x0 x1,
      eval_op2_no_side_effect
        (ano_lo lo_or)
        x0
        x1
        (match x0, x1 with | 0%Z, 0%Z => 0%Z | _, _ => 1%Z end)
  | eval_op2_gt :
    forall x0 x1,
      eval_op2_no_side_effect (ano_ro ro_gt) x0 x1 (if Z.gtb x0 x1 then 1%Z else 0%Z)
  | eval_op2_ge :
    forall x0 x1,
      eval_op2_no_side_effect (ano_ro ro_ge) x0 x1 (if Z.geb x0 x1 then 1%Z else 0%Z)
  | eval_op2_lt :
    forall x0 x1,
      eval_op2_no_side_effect (ano_ro ro_lt) x0 x1 (if Z.ltb x0 x1 then 1%Z else 0%Z)
  | eval_op2_le :
    forall x0 x1,
      eval_op2_no_side_effect (ano_ro ro_le) x0 x1 (if Z.leb x0 x1 then 1%Z else 0%Z)
  | eval_op2_eq :
    forall x0 x1,
      eval_op2_no_side_effect (ano_ro ro_eq) x0 x1 (if Z.eqb x0 x1 then 1%Z else 0%Z)
  | eval_op2_neq :
    forall x0 x1,
      eval_op2_no_side_effect (ano_ro ro_gt) x0 x1 (if Z.eqb x0 x1 then 0%Z else 1%Z)
  | eval_op2_bo_and :
    forall x0 x1,
      eval_op2_no_side_effect (ano_bo bo_and) x0 x1 (Z.land x0 x1)
  | eval_op2_bo_or :
    forall x0 x1,
      eval_op2_no_side_effect (ano_bo bo_or) x0 x1 (Z.lor x0 x1)
  | eval_op2_bo_xor :
    forall x0 x1,
      eval_op2_no_side_effect (ano_bo bo_xor) x0 x1 (Z.lxor x0 x1)
  | eval_op2_bo_rshift :
    forall x0 x1,
      (x1 >= 0)%Z ->
        eval_op2_no_side_effect (ano_bo bo_rshift) x0 x1 (Z.shiftr x0 x1)
  | eval_op2_bo_lshift :
    forall x0 x1,
      (x1 >= 0)%Z ->
        eval_op2_no_side_effect (ano_bo bo_lshift) x0 x1 (Z.shiftl x0 x1).

Module Type State.
  Parameter state : Type.
  Parameter resolve : state -> reference -> Z -> Prop.
  Parameter update : state -> state -> reference -> Z -> Prop.
  Axiom update_effect :
    forall st0 st1 ref0 x0,
      update st0 st1 ref0 x0 -> (
        resolve st1 ref0 x0
        /\ (
          forall ref1 x1,
            ref1 <> ref0 ->
              resolve st0 ref1 x1 ->
                resolve st1 ref1 x1)).
  Parameter read_bitstream : state -> state -> reference -> parsing_descriptor -> Z -> Prop.
  Parameter resolve_function : state -> string -> list string -> statement -> Prop.
End State.

Module eval_module (S : State).

  Definition eval_func_type : Type :=
    S.state -> S.state -> string -> list Z -> Z -> Prop.

  Definition eval_expr_type : Type :=
    expression -> S.state -> S.state -> expr_result -> Prop.

  Module eval_stmt_module.

    Parameter eval_func_prop : eval_func_type.

    Inductive chained_eval_expr (eval_expr_prop : eval_expr_type) : list S.state -> list expression -> list Z -> Prop :=
      | chained_eval_expr_nil :
        forall s,
          chained_eval_expr eval_expr_prop [s] [] []
      | chained_eval_expr_more :
        forall s0 s1 ss e0 es z0 zs,
          eval_expr_prop e0 s0 s1 (er_value z0) ->
            chained_eval_expr eval_expr_prop (s1 :: ss) es zs ->
              chained_eval_expr eval_expr_prop (s0 :: s1 :: ss) (e0 :: es) (z0 :: zs).

    (* TODO: add more rules *)
    (* Note: order of evaluation of subexpressions is fixed:
       left first, then right. *)
    Inductive eval_expr : eval_expr_type :=
      | eval_expr_number :
        forall st x,
          expr_number x // st \\ st \\ er_value x
      | eval_expr_variable :
        forall st label,
          expr_variable label // st \\ st \\ er_reference (ref_variable label [])
      | eval_expr_subscript :
        forall e0 e1 st0 st1 st2 label indices x,
          e0 // st0 \\ st1 \\ er_reference (ref_variable label indices) ->
            e1 // st1 \\ st2 \\ er_value x ->
              expr_op2 (ano_so so_subscript) e0 e1 // st0 \\ st2 \\
                er_reference (ref_variable label (indices ++ [x]))
      | eval_expr_op1_no_side_effect :
        forall e x y st0 st1 op,
          e // st0 \\ st1 \\ er_value x ->
            eval_op1_no_side_effect op x y ->
              expr_op1 op e // st0 \\ st1 \\ er_value y
      | eval_expr_op2_no_side_effect :
        forall e0 e1 x0 x1 y st0 st1 st2 op,
          e0 // st0 \\ st1 \\ er_value x0 ->
            e1 // st1 \\ st2 \\ er_value x1 ->
              eval_op2_no_side_effect op x0 x1 y ->
                expr_op2 (ano_ao ao_plus) e0 e1 // st0 \\ st2 \\ er_value y
      | eval_expr_assign :
        forall e0 e1 x st0 st1 st2 st3 ref,
          e0 // st0 \\ st1 \\ er_reference ref ->
            e1 // st1 \\ st2 \\ er_value x ->
              S.update st2 st3 ref x ->
                expr_op2 (ano_aso aso_assign) e0 e1 // st0 \\ st3 \\ er_reference ref
      | eval_expr_postinc :
        forall e x st0 st1 st2 ref,
          e // st0 \\ st1 \\ er_reference ref ->
            S.resolve st1 ref x ->
              S.update st1 st2 ref (x + 1) ->
                expr_op1 (ano_aso aso_postinc) e // st0 \\ st2 \\ er_value x
      | eval_expr_postdec :
        forall e x st0 st1 st2 ref,
          e // st0 \\ st1 \\ er_reference ref ->
            S.resolve st1 ref x ->
              S.update st1 st2 ref (x - 1) ->
                expr_op1 (ano_aso aso_postinc) e // st0 \\ st2 \\ er_value x
      | eval_expr_addassign :
        forall e0 e1 x0 x1 st0 st1 st2 st3 ref,
          e0 // st0 \\ st1 \\ er_reference ref ->
            e1 // st1 \\ st2 \\ er_value x1 ->
              S.resolve st2 ref x0 ->
                S.update st2 st3 ref (x0 + x1) ->
                 expr_op2 (ano_aso aso_addassign) e0 e1 // st0 \\ st3 \\ er_reference ref
      | eval_expr_subassign :
        forall e0 e1 x0 x1 st0 st1 st2 st3 ref,
          e0 // st0 \\ st1 \\ er_reference ref ->
            e1 // st1 \\ st2 \\ er_value x1 ->
              S.resolve st2 ref x0 ->
                S.update st2 st3 ref (x0 - x1) ->
                 expr_op2 (ano_aso aso_addassign) e0 e1 // st0 \\ st3 \\ er_reference ref
      | eval_expr_mulassign :
        forall e0 e1 x0 x1 st0 st1 st2 st3 ref,
          e0 // st0 \\ st1 \\ er_reference ref ->
            e1 // st1 \\ st2 \\ er_value x1 ->
              S.resolve st2 ref x0 ->
                S.update st2 st3 ref (x0 * x1) ->
                 expr_op2 (ano_aso aso_addassign) e0 e1 // st0 \\ st3 \\ er_reference ref
      | eval_expr_divassign :
        forall e0 e1 x0 x1 st0 st1 st2 st3 ref,
          e0 // st0 \\ st1 \\ er_reference ref ->
            e1 // st1 \\ st2 \\ er_value x1 ->
              S.resolve st2 ref x0 ->
                S.update st2 st3 ref (Z.quot x0 x1) ->
                 expr_op2 (ano_aso aso_addassign) e0 e1 // st0 \\ st3 \\ er_reference ref
      | eval_expr_borassign :
        forall e0 e1 x0 x1 st0 st1 st2 st3 ref,
          e0 // st0 \\ st1 \\ er_reference ref ->
            e1 // st1 \\ st2 \\ er_value x1 ->
              S.resolve st2 ref x0 ->
                S.update st2 st3 ref (Z.lor x0 x1) ->
                 expr_op2 (ano_aso aso_addassign) e0 e1 // st0 \\ st3 \\ er_reference ref
      | eval_expr_bandassign :
        forall e0 e1 x0 x1 st0 st1 st2 st3 ref,
          e0 // st0 \\ st1 \\ er_reference ref ->
            e1 // st1 \\ st2 \\ er_value x1 ->
              S.resolve st2 ref x0 ->
                S.update st2 st3 ref (Z.land x0 x1) ->
                 expr_op2 (ano_aso aso_addassign) e0 e1 // st0 \\ st3 \\ er_reference ref
      | eval_expr_xorassign :
        forall e0 e1 x0 x1 st0 st1 st2 st3 ref,
          e0 // st0 \\ st1 \\ er_reference ref ->
            e1 // st1 \\ st2 \\ er_value x1 ->
              S.resolve st2 ref x0 ->
                S.update st2 st3 ref (Z.lxor x0 x1) ->
                 expr_op2 (ano_aso aso_addassign) e0 e1 // st0 \\ st3 \\ er_reference ref
      | eval_expr_reference :
        forall st ref x e,
          S.resolve st ref x ->
            e // st \\ st \\ er_reference ref ->
              e // st \\ st \\ er_value x
      | eval_expr_func :
        forall st0 states st1 st2 args_expr args_val function_name result,
          chained_eval_expr eval_expr ([st0] ++ states ++ [st1]) args_expr args_val ->
            eval_func_prop st1 st2 function_name args_val result ->
              expr_op1n (ano_so so_function_call) (expr_variable function_name) args_expr // st0 \\ st2 \\ er_value result
      | eval_expr_turnary_true :
        forall st0 st1 st2 e0 e1 e2 x er,
          e0 // st0 \\ st1 \\ er_value x ->
            x <> 0%Z ->
              e1 // st1 \\ st2 \\ er ->
                expr_op1n (ano_so so_turnary) e0 [e1; e2] // st0 \\ st2 \\ er
      | eval_expr_turnary_false :
        forall st0 st1 st2 e0 e1 e2 x er,
          e0 // st0 \\ st1 \\ er_value x ->
            x = 0%Z ->
              e2 // st1 \\ st2 \\ er ->
                expr_op1n (ano_so so_turnary) e0 [e1; e2] // st0 \\ st2 \\ er
    where "e '//' st '\\' st' '\\' v" := (eval_expr e st st' v).

    (* TODO: add more rules *)
    (*
    Inductive eval_stmt : statement -> state -> state -> Prop :=
      | eval_stmt_expression :
        forall st st' e v,
          e // st \\ st' \\ v ->
            stmt_expression e / st \\ st'
      | eval_stmt_syntax_element_simple :
        forall st0 st1 st2 e ref pd,
          e // st0 \\ st1 \\ er_reference ref ->
            expr_op1n (expr_variable 
           stmt_syntax_element (expr_variable label) / st \\ st & 
    with
      eval_expr : expression -> state -> state -> value -> Prop :=
      | eval_expr_number :
        forall st x,
          expr_number x // st \\ st \\ val_variable x
      | eval_expr_variable :
        forall st label x,
          st label = Some (val_variable x) ->
            expr_variable label // st \\ st \\ val_variable x
    where "c '/' st '\\' st'" := (eval_stmt c st st')
    and "e '//' st '\\' st' '\\' v" := (eval_expr e st st' v).
    *)

  End eval_stmt_module.

  Module eval_func_module.

    Parameter eval_expr : eval_expr_type.

  End eval_func_module.

End eval_module.

End syntax_processor.