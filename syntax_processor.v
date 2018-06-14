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

(* An identifier may refere to either a single variable, array of variables,
   or declaration (of function, of constant or of array of constants). *)
Inductive value :=
  | val_variable : Z -> value
  | val_array : (list Z -> Z) -> value
  | val_decl : declaration -> value.
Definition state := partial_map value.

Example state_update_notation_ex0 :
  empty & {{ "a"%string --> (val_variable 3) }} "a"%string = Some (val_variable 3).
Proof. reflexivity. Qed.

Reserved Notation "e '//' st '\\' st' \\ x" (at level 50, left associativity).
Reserved Notation "s '/' st '\\' st'" (at level 40, st at level 39).

(* TODO: add more rules *)
Inductive
  eval_stmt : statement -> state -> state -> Prop :=
  | eval_stmt_expression :
    forall st st' e v,
      e // st \\ st' \\ v ->
      stmt_expression e / st \\ st'
with
  eval_expr : expression -> state -> state -> value -> Prop :=
  | eval_expr_number :
    forall st x,
      expr_number x // st \\ st \\ val_variable x
where "c '/' st '\\' st'" := (eval_stmt c st st')
and "e '//' st '\\' st' '\\' v" := (eval_expr e st st' v).

End syntax_processor.