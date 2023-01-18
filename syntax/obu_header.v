Require Import Fin.
Require Import List.
Require Import ZArith.
Import ListNotations.

Require Import formal_av1.basic_types.
Require Import formal_av1.entropy.descriptors.
Require formal_av1.structures.

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

Inductive obu_header_decode_relation : list bit -> structures.obu_header_type -> Prop :=
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
        (structures.obu_type_enum.to_nat obu_type_value) ->
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
          structures.make_obu_header
              obu_forbidden_bit_value
              obu_type_value
              obu_extension_flag_value
              obu_has_size_field_value
              obu_reserved_1bit_value
              temporal_id_value
              spatial_id_value
              extension_header_reserved_3bits_value).
