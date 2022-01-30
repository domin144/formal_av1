Require Import List ZArith.
Import ListNotations.

Require Import formal_av1.basic_types.

Module bit_index_order.

  Definition t := byte.bit_index.

  Inductive is_next (a b : t) : Prop :=
  | is_index_intro :
    proj1_sig (Fin.to_nat a) = S (proj1_sig (Fin.to_nat b)) ->
      is_next a b.

  Inductive is_previous (a b : t) : Prop :=
    | is_previous_intro :
      is_next b a -> is_previous a b.

  Inductive is_last (a : t) : Prop :=
    | is_last_intro :
      ~(exists b, is_next a b) -> is_last a.

  Inductive is_first (a : t) : Prop :=
    | is_first_intro :
      ~(exists b, is_previous a b) -> is_first a.

End bit_index_order.

Module bitstream_position.

  Record t := t_intro {
    byte_index : nat;
    bit_index : byte.bit_index;
  }.

  (* Bitstream positions go from most significant bit to least significant bit. *)

  Inductive is_next : t -> t -> Prop :=
    | is_next_same_byte :
      forall bit_pos_a bit_pos_b,
        bit_index_order.is_previous bit_pos_a bit_pos_b ->
      forall byte_pos, is_next
        (t_intro byte_pos bit_pos_a)
        (t_intro byte_pos bit_pos_b)
    | is_next_next_byte :
      forall bit_pos_a, bit_index_order.is_first bit_pos_a ->
      forall bit_pos_b, bit_index_order.is_last bit_pos_b ->
      forall byte_pos, is_next
        (t_intro byte_pos bit_pos_a)
        (t_intro (S byte_pos) bit_pos_b).

  Inductive is_previous (bit_pos_a bit_pos_b : t) : Prop :=
    | is_previous_intro :
      is_next bit_pos_b bit_pos_a ->
      is_previous bit_pos_a bit_pos_b.

End bitstream_position.

Inductive bit_in_byte_relation
    (bt : byte.t)
    (index : byte.bit_index)
    (b : bit)
    : Prop :=
  | bit_in_byte_intro :
    Vector.nth bt index = b -> bit_in_byte_relation bt index b.

Inductive byte_in_obu_relation :
    open_bitstream_unit -> nat -> byte.t -> Prop :=
  byte_in_bitstream_relation_intro:
    forall obu bp b,
      nth_error obu bp = Some b ->
        byte_in_obu_relation obu bp b.

Inductive obu_at_relation :
    open_bitstream_unit -> bitstream_position.t -> bit -> Prop :=
  obu_at_relation_intro :
    forall obu byte_index bit_index byte value,
      byte_in_obu_relation obu byte_index byte ->
      bit_in_byte_relation byte bit_index value ->
      obu_at_relation obu (bitstream_position.t_intro byte_index bit_index)
        value.

Inductive read_bit_relation
    (obu : open_bitstream_unit)
    (bp_0 : bitstream_position.t)
    (b : bit)
    (bp_1 : bitstream_position.t)
    : Prop :=
  | read_bit_relation_intro :
    obu_at_relation obu bp_0 b ->
    bitstream_position.is_next bp_0 bp_1 ->
    read_bit_relation obu bp_0 b bp_1.

Inductive read_bit_list_relation
    (obu : open_bitstream_unit)
    (bp_a : bitstream_position.t)
    (bp_b : bitstream_position.t)
    : list bit -> Prop :=
  | read_bit_list_relation_first :
    forall (b : bit),
    read_bit_relation obu bp_a b bp_b ->
    read_bit_list_relation obu bp_a bp_b [b]
  | read_bit_list_relation_next :
    forall (b : bit) (l : list bit) (bp_a_next : bitstream_position.t),
    read_bit_relation obu bp_a b bp_a_next ->
    read_bit_list_relation obu bp_a_next bp_b l ->
    read_bit_list_relation obu bp_a bp_b (b :: l).