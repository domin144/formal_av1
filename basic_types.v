Require Import String.
Require Import ZArith.

Inductive pseudocode : Type :=
  | pseudocode_intro : string -> pseudocode.

Inductive arithmetic_operator : Type :=
  | ao_plus
  | ao_minus
  | ao_minus_unary
  | ao_mult
  | ao_div
  | ao_mod.

Inductive logical_operator : Type :=
  | lo_and
  | lo_or
  | lo_not.

Inductive relational_operator : Type :=
  | ro_gt
  | ro_ge
  | ro_lt
  | ro_le
  | ro_eq
  | ro_neq.

Inductive bitwise_operator : Type :=
  | bo_and
  | bo_or
  | bo_xor
  | bo_neg
  | bo_rshift
  | bo_lshift.

Inductive assignment_operator : Type :=
  | aso_assign
  | aso_postinc
  | aso_postdec
  | aso_addassign
  | aso_subassign
  | aso_mulassign
  | aso_divassign.

Inductive special_operator : Type :=
  | so_function_call
  | so_subscript
  | so_tunrary.

Inductive any_operator :=
  | ano_ao : arithmetic_operator -> any_operator
  | ano_lo : logical_operator -> any_operator
  | ano_ro : relational_operator -> any_operator
  | ano_bo : bitwise_operator -> any_operator
  | ano_aso : assignment_operator -> any_operator
  | ano_so : special_operator -> any_operator.

Inductive expression : Type :=
  | expr_number : Z -> expression
  | expr_variable : string -> expression
  | expr_op1 : any_operator -> expression -> expression
  | expr_op2 : any_operator -> expression -> expression -> expression
  | expr_op1n : any_operator -> expression -> list expression -> expression.

Inductive parsing_descriptor : Type :=
  | pd_fixed : expression -> parsing_descriptor
  | pd_little_endian : expression -> parsing_descriptor
  | pd_signed : expression -> parsing_descriptor
  | pd_ae_literal : expression -> parsing_descriptor
  | pd_ae_alphabet : parsing_descriptor
  | pd_ae_unsigned : expression -> parsing_descriptor.

Inductive statement : Type :=
  | stmt_expression : expression -> statement
  | stmt_syntax_element : expression -> parsing_descriptor -> statement
  | stmt_group : list statement -> statement
  | stmt_while : expression -> statement -> statement
  | stmt_do_while : statement -> expression -> statement
  | stmt_if : expression -> statement -> statement
  | stmt_if_else : expression -> statement -> statement -> statement
  | stmt_for : expression -> expression -> expression -> statement -> statement
  | stmt_return : expression -> statement
  | stmt_empty : statement.

Inductive declaration : Type :=
  | decl_constant : string -> expression -> declaration
  | decl_constant_array :
    string -> list expression -> list expression -> declaration
  | decl_function : string -> list string -> statement -> declaration.
