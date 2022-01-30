Require Import List ZArith.
Import ListNotations.

Require Import formal_av1.basic_types.
Require Import formal_av1.entropy.bitstream_position.

(* AV-1 spec 4.10 Descriptors *)

Inductive descriptor : Set :=
  | descriptor_f : nat -> descriptor
  | descriptor_uvlc : descriptor
  | descriptor_le : nat -> descriptor
  | descriptor_leb128 : descriptor
  | descriptor_su : nat -> descriptor
  | descriptor_ns : nat -> descriptor
  | descriptor_L : nat -> descriptor
  | descriptor_S : descriptor
  | descriptor_NS : nat -> descriptor.

Definition bit_to_nat (b : bit) : nat :=
  match b with
  | bit_0 => 0
  | bit_1 => 1
  end.

Inductive f_decode_relation : nat -> list bit -> nat -> Prop :=
  | f_decode_relation_nil :
    f_decode_relation 0 [] 0
  | f_decode_relation_next :
    forall n bs b x,
    f_decode_relation n bs x ->
    f_decode_relation (S n) (bs ++ [b]) (2 * x + (bit_to_nat b)).
