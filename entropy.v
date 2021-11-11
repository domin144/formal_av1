Require Import List ZArith.

Require Import formal_av1.basic_types.

Record bitstream_position := bitstream_postion_intro {
  byte_index : nat;
  bit_index : bit_in_byte_index;
}.

Inductive bit_in_byte_relation :
    byte -> bit_in_byte_index -> bit -> Prop :=
    | bit_0_in_byte_intro :
      forall b0 b1 b2 b3 b4 b5 b6 b7,
        bit_in_byte_relation (byte_intro b0 b1 b2 b3 b4 b5 b6 b7) 0 b0
    | bit_1_in_byte_intro :
      forall b0 b1 b2 b3 b4 b5 b6 b7,
        bit_in_byte_relation (byte_intro b0 b1 b2 b3 b4 b5 b6 b7) 1 b1
    | bit_2_in_byte_intro :
      forall b0 b1 b2 b3 b4 b5 b6 b7,
        bit_in_byte_relation (byte_intro b0 b1 b2 b3 b4 b5 b6 b7) 2 b2
    | bit_3_in_byte_intro :
      forall b0 b1 b2 b3 b4 b5 b6 b7,
        bit_in_byte_relation (byte_intro b0 b1 b2 b3 b4 b5 b6 b7) 3 b3
    | bit_4_in_byte_intro :
      forall b0 b1 b2 b3 b4 b5 b6 b7,
        bit_in_byte_relation (byte_intro b0 b1 b2 b3 b4 b5 b6 b7) 4 b4
    | bit_5_in_byte_intro :
      forall b0 b1 b2 b3 b4 b5 b6 b7,
        bit_in_byte_relation (byte_intro b0 b1 b2 b3 b4 b5 b6 b7) 5 b5
    | bit_6_in_byte_intro :
      forall b0 b1 b2 b3 b4 b5 b6 b7,
        bit_in_byte_relation (byte_intro b0 b1 b2 b3 b4 b5 b6 b7) 6 b6
    | bit_7_in_byte_intro :
      forall b0 b1 b2 b3 b4 b5 b6 b7,
        bit_in_byte_relation (byte_intro b0 b1 b2 b3 b4 b5 b6 b7) 7 b7.

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

(* Inductive read_bit_relation :
    bitstream -> bitstream_position -> bit -> bitstream_position -> Prop :=
  | read_bit_relation_intro :
    forall bs bp0 b bp1,
*)