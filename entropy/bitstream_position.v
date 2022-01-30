Require Import List ZArith.

Require Import formal_av1.basic_types.

Record bitstream_position := bitstream_postion_intro {
  byte_index : nat;
  bit_index : bit_in_byte_index;
}.

Inductive next_bit_index_relation (a b : bit_in_byte_index) : Prop :=
  | next_bit_index_intro :
    proj1_sig (Fin.to_nat a) = S (proj1_sig (Fin.to_nat b)) ->
      next_bit_index_relation a b.

Inductive previous_bit_index_relation (a b : bit_in_byte_index) : Prop :=
  | previous_bit_index_intro :
    next_bit_index_relation b a -> previous_bit_index_relation a b.

Inductive last_bit_index_property (a : bit_in_byte_index) : Prop :=
  | last_bit_index_intro :
    ~(exists b, next_bit_index_relation a b) -> last_bit_index_property a.

Inductive first_bit_index_property (a : bit_in_byte_index) : Prop :=
  | first_bit_index_intro :
    ~(exists b, previous_bit_index_relation a b) -> first_bit_index_property a.

(* Bitstream positions go from most significant bit to least significant bit. *)

Inductive next_bitstream_position_relation
    : bitstream_position -> bitstream_position -> Prop :=
  | next_bitstream_position_same_byte :
    forall bit_pos_a bit_pos_b,
      previous_bit_index_relation bit_pos_a bit_pos_b ->
    forall byte_pos, next_bitstream_position_relation
      (bitstream_postion_intro byte_pos bit_pos_a)
      (bitstream_postion_intro byte_pos bit_pos_b)
  | next_bitstream_position_next_byte :
  forall bit_pos_a, first_bit_index_property bit_pos_a ->
  forall bit_pos_b, last_bit_index_property bit_pos_b ->
  forall byte_pos, next_bitstream_position_relation
    (bitstream_postion_intro byte_pos bit_pos_a)
    (bitstream_postion_intro (S byte_pos) bit_pos_b).

Inductive bit_in_byte_relation
      (bt : byte)
      (index : bit_in_byte_index)
      (b : bit)
      : Prop :=
  | bit_in_byte_intro :
    Vector.nth bt index = b -> bit_in_byte_relation bt index b.

Inductive byte_in_obu_relation :
    open_bitstream_unit -> nat -> byte -> Prop :=
  byte_in_bitstream_relation_intro:
    forall obu bp b,
      nth_error obu bp = Some b ->
        byte_in_obu_relation obu bp b.

Inductive obu_at_relation :
    open_bitstream_unit -> bitstream_position -> bit -> Prop :=
  obu_at_relation_intro :
    forall obu byte_index bit_index byte value,
      byte_in_obu_relation obu byte_index byte ->
      bit_in_byte_relation byte bit_index value ->
      obu_at_relation obu (bitstream_postion_intro byte_index bit_index)
        value.

Inductive read_bit_relation
    (obu : open_bitstream_unit)
    (bp_0 : bitstream_position)
    (b : bit)
    (bp_1 : bitstream_position)
    : Prop :=
  | read_bit_relation_intro :
    obu_at_relation obu bp_0 b ->
    next_bitstream_position_relation bp_0 bp_1 ->
    read_bit_relation obu bp_0 b bp_1.
