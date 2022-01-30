Require Import List ZArith.

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
