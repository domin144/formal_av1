Require Import List ZArith.
Import ListNotations.

Require Import basic_types.
Require Import pseudocodes.
Require Import parser.
(* Maps are copied from logical foundations.
   TODO: Might want to replace with FMapAVL. *)
Require Import Maps.

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

(* An expression might evaluate to reference to single variable or array element.
   Reference to single variable is label with empty subscrtip list. *)
Inductive reference :=
  | ref_variable : string -> list Z -> reference.

Definition state := reference -> Z.

Definition empty_state (ref : reference) : Z := 0.

Example state_ex0 :
  empty_state (ref_variable "terefere" nil) = 0%Z.
Proof. reflexivity. Qed.

Reserved Notation "e '//' st '\\' st' \\ x" (at level 50, left associativity).
Reserved Notation "s '/' st '\\' st'" (at level 40, st at level 39).

Inductive eval_expr : expression -> state -> state -> value -> Prop :=
  | eval_expr_number :
    forall st x,
      expr_number x // st \\ st \\ val_variable x
  | eval_expr_variable :
    forall st label x,
      st label = Some (val_variable x) ->
        expr_variable label // st \\ st \\ val_variable x
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