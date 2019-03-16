Require Import List ZArith.
Import ListNotations.

Require Import basic_types.
Require Import pseudocodes.
Require Import parser.
Require Import state.

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

Reserved Notation "e '//' st '\\' st' \\ x" (at level 50, left associativity).
Reserved Notation "s '/' st '\\' st'" (at level 40, st at level 39).

Inductive expr_result : Type :=
  | er_value : Z -> expr_result
  | er_reference : reference -> expr_result.

Fixpoint binary_negation (x : Z) : Z := -x - 1.

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

(* TODO: add more rules *)
(* Note: order of evaluation of subexpressions is fixed:
   left first, then right. *)
Inductive eval_expr : expression -> state -> state -> expr_result -> Prop :=
  | eval_expr_number :
    forall st x,
      expr_number x // st \\ st \\ er_value x
  | eval_expr_variable :
    forall st label,
      expr_variable label // st \\ st \\ er_reference (ref_variable label [])
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
  | eval_expr_reference :
    forall st ref x e,
      st ref = Some x ->
        e // st \\ st \\ er_reference ref ->
          e // st \\ st \\ er_value x
where "e '//' st '\\' st' '\\' v" := (eval_expr e st st' v).

(* TODO: add more rules *)
Inductive
  eval_stmt : statement -> state -> state -> Prop :=
  | eval_stmt_expression :
    forall st st' e v,
      e // st \\ st' \\ v ->
        stmt_expression e / st \\ st'
  | eval_stmt_syntax_element_simple :
    forall label pd,
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

End syntax_processor.