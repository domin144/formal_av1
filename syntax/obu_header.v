Require Import Fin.
Require Import List.
Require Import ZArith.
Require Import formal_av1.basic_types.
Require Import formal_av1.entropy.descriptors.
Import ListNotations.

Inductive conditional_decode_relation
    {X : Set}
    (condition : Prop)
    (true_decode_relation : list bit -> X -> Prop)
    (default_value : X) :
    list bit -> X -> Prop :=
  | conditional_decode_true :
    condition ->
    forall bits value,
    true_decode_relation bits value ->
    conditional_decode_relation
        condition
        true_decode_relation
        default_value
        bits
        value
  | conditional_decode_false :
    ~ condition ->
    conditional_decode_relation
        condition
        true_decode_relation
        default_value
        []
        default_value.

(* TODO: move enums somewhere else *)
Module obu_type_enum.

  Inductive t : Set :=
    | Reserved_0
    | OBU_SEQUENCE_HEADER
    | OBU_TEMPORAL_DELIMITER
    | OBU_FRAME_HEADER
    | OBU_TILE_GROUP
    | OBU_METADATA
    | OBU_FRAME
    | OBU_REDUNDANT_FRAME_HEADER
    | OBU_TILE_LIST
    | Reserved_9
    | Reserved_10
    | Reserved_11
    | Reserved_12
    | Reserved_13
    | Reserved_14
    | OBU_PADDING.

  Definition to_nat (x : t) : nat :=
      match x with
      | Reserved_0                  =>  0
      | OBU_SEQUENCE_HEADER         =>  1
      | OBU_TEMPORAL_DELIMITER      =>  2
      | OBU_FRAME_HEADER            =>  3
      | OBU_TILE_GROUP              =>  4
      | OBU_METADATA                =>  5
      | OBU_FRAME                   =>  6
      | OBU_REDUNDANT_FRAME_HEADER  =>  7
      | OBU_TILE_LIST               =>  8
      | Reserved_9                  =>  9
      | Reserved_10                 => 10
      | Reserved_11                 => 11
      | Reserved_12                 => 12
      | Reserved_13                 => 13
      | Reserved_14                 => 14
      | OBU_PADDING                 => 15
      end.

End obu_type_enum.

(* Definition fin_by_bits (n : nat) : Set :=
  Fin.t (2 ^ n).

Record obu_header : Set := make_obu_header
{
  obu_forbidden_bit : fin_by_bits 1;
  obu_type : obu_type_enum.t;
  obu_extension_flag : fin_by_bits 1;
  obu_has_size_field : bool;
  obu_reserved_1bit : fin_by_bits 1;
  temporal_id : fin_by_bits 3;
  spatial_id : fin_by_bits 2;
  extension_header_reserved_3bits : fin_by_bits 3
}. *)

Record obu_header : Set := make_obu_header
{
  obu_forbidden_bit : nat;
  obu_type : obu_type_enum.t;
  obu_extension_flag : bool;
  obu_has_size_field : bool;
  obu_reserved_1bit : nat;
  temporal_id : nat;
  spatial_id : nat;
  extension_header_reserved_3bits : nat
}.

Inductive obu_header_decode_relation : list bit -> obu_header -> Prop :=
  obu_header_decode_intro :
    forall
        obu_forbidden_bit_bits
        obu_forbidden_bit_value
        obu_type_bits
        obu_type_value
        obu_extension_flag_bits
        obu_extension_flag_value
        obu_has_size_field_bits
        obu_has_size_field_value
        obu_reserved_1bit_bits
        obu_reserved_1bit_value
        temporal_id_bits
        temporal_id_value
        spatial_id_bits
        spatial_id_value
        extension_header_reserved_3bits_bits
        extension_header_reserved_3bits_value,
    f_decode_relation
        1
        obu_forbidden_bit_bits
        obu_forbidden_bit_value ->
    f_decode_relation
        3
        obu_type_bits
        (obu_type_enum.to_nat obu_type_value) ->
    f_decode_relation
        1
        obu_extension_flag_bits
        (Nat.b2n obu_extension_flag_value) ->
    f_decode_relation
        1
        obu_has_size_field_bits
        (Nat.b2n obu_has_size_field_value) ->
    f_decode_relation
        1
        obu_reserved_1bit_bits
        obu_reserved_1bit_value ->
    conditional_decode_relation
        (obu_extension_flag_value = true)
        (f_decode_relation 3)
        0
        temporal_id_bits
        temporal_id_value ->
    conditional_decode_relation
        (obu_extension_flag_value = true)
        (f_decode_relation 2)
        0
        spatial_id_bits
        spatial_id_value ->
    conditional_decode_relation
        (obu_extension_flag_value = true)
        (f_decode_relation 3)
        0
        extension_header_reserved_3bits_bits
        extension_header_reserved_3bits_value ->
    obu_header_decode_relation
        (
          obu_forbidden_bit_bits
          ++ obu_type_bits
          ++ obu_extension_flag_bits
          ++ obu_has_size_field_bits
          ++ obu_reserved_1bit_bits
          ++ temporal_id_bits
          ++ spatial_id_bits
          ++ extension_header_reserved_3bits_bits)
        (
          make_obu_header
              obu_forbidden_bit_value
              obu_type_value
              obu_extension_flag_value
              obu_has_size_field_value
              obu_reserved_1bit_value
              temporal_id_value
              spatial_id_value
              extension_header_reserved_3bits_value).
