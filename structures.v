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

Record obu_header_type : Set := make_obu_header
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
