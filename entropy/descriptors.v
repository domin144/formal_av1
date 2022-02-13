Require Import List ZArith.
Import ListNotations.

Require Import formal_av1.basic_types.
Require Import formal_av1.entropy.bitstream_position.

(* AV-1 spec 4.10. Descriptors *)

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

(* AV-1 spec 4.10.2. f(n) *)
(* AV-1 spec 8.1. Parsing process for f(n) *)

Inductive f_decode_relation : nat -> list bit -> nat -> Prop :=
  | f_decode_relation_nil :
    f_decode_relation 0 [] 0
  | f_decode_relation_next :
    forall n bs b x,
    f_decode_relation n bs x ->
    f_decode_relation (S n) (bs ++ [b]) (2 * x + (bit_to_nat b)).

(* AV-1 spec 4.10.3. uvlc() *)

Inductive uvlc_decode_relation : list bit -> nat -> Prop :=
  | uvlc_decode_less_32 :
    forall leading_zeros, leading_zeros < 32 ->
    forall value l, f_decode_relation leading_zeros l value ->
    uvlc_decode_relation
      ((repeat bit_0 leading_zeros) ++ [bit_1] ++ l)
      (value + 2 ^ leading_zeros - 1)
  | uvlc_decode_over_32 :
    forall leading_zeros, leading_zeros >= 32 ->
    uvlc_decode_relation
      ((repeat bit_0 leading_zeros) ++ [bit_1])
      (2 ^ 32 - 1).

(* AV-1 spec 4.10.4. le(n) *)

Inductive le_decode_relation : nat -> list bit -> nat -> Prop :=
  | le_decode_relation_nil :
    le_decode_relation 0 [] 0
  | le_decode_relation_next :
    forall n l_0 l_more x_0 x_more,
    f_decode_relation byte.bits_count l_0 x_0 ->
    le_decode_relation n l_more x_more ->
    le_decode_relation 
      (S n)
      (l_0 ++ l_more)
      (x_0 + 2 ^ byte.bits_count * x_more).

(* AV-1 spec 4.10.5. leb128() *)
(* Continuation bit can only be 1, if i < 7. *)

Inductive leb128_helper (i : nat) : list bit -> nat -> Prop :=
  | leb128_helper_stop_bit :
    forall data_bits x, f_decode_relation 7 data_bits x ->
    leb128_helper i ([bit_0] ++ data_bits) x
  | leb128_helper_more :
    i < 7 ->
    forall data_bits x, f_decode_relation 7 data_bits x ->
    forall bits_more x_more, leb128_helper (S i) bits_more x_more ->
    leb128_helper i ([bit_1] ++ data_bits ++ bits_more) (x + 2 ^ 7 * x_more).

Inductive leb128_decode_relation (bits : list bit) (x : nat) : Prop :=
  | leb128_decode_relation_intro :
    x < 2 ^ 32 ->
    leb128_helper 0 bits x ->
    leb128_decode_relation bits x.

(* AV-1 spec 4.10.6. su(n) *)

Inductive su_decode_relation : nat -> list bit -> Z -> Prop :=
  | su_decode_non_negative :
    forall i bits x,
    f_decode_relation i bits x ->
    su_decode_relation (S i) ([bit_0] ++ bits) (Z.of_nat x)
  | su_decode_negative :
    forall i bits x,
    f_decode_relation i bits x ->
    su_decode_relation
      (S i)
      ([bit_1] ++ bits)
      (- (2 ^ (Z.of_nat i)) + Z.of_nat x).

(* AV-1 spec 4.10.7. ns(n) *)

Inductive ns_w_relation (n w : nat) : Prop :=
  | ns_w_intro :
    2 ^ (w - 1) <= n ->
    n < 2 ^ w ->
    ns_w_relation n w.

Inductive ns_m_relation (n : nat) : nat -> Prop :=
  | ns_m_intro :
    forall w, ns_w_relation n w ->
    ns_m_relation n (2 ^ w - n).

Inductive ns_decode_relation (n : nat) : list bit -> nat -> Prop :=
  | ns_decode_short :
    forall w, ns_w_relation n w ->
    forall m, ns_m_relation n m ->
    forall x, x < m ->
    forall bits, f_decode_relation (w - 1) bits x ->
    ns_decode_relation n bits x
  | ns_decode_long :
    forall w, ns_w_relation n w ->
    forall m, ns_m_relation n m ->
    forall x, x >= m ->
    (* note: 2 * m <= m + x < 2 ^ w *)
    forall bits, f_decode_relation w bits (m + x) ->
    ns_decode_relation n bits x.
