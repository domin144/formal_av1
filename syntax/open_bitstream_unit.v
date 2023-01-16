Require Import List.
Require Import ZArith.
Require Import formal_av1.basic_types.
Require Import formal_av1.syntax.obu_header.
Import ListNotations.

Record sequence_header_obu_type : Set := make_sequence_header_obu
{ (* TODO *) }.
Record temporal_delimiter_obu_type : Set := make_temporal_delimiter_obu
{ (* TODO *) }.
Record frame_header_obu_type : Set := make_frame_header_obu
{ (* TODO *) }.
Record tile_group_obu_type : Set := make_tile_group_obu
{ (* TODO *) }.
Record metadata_obu_type : Set := make_metadata_obu
{ (* TODO *) }.
Record frame_obu_type : Set := make_frame_obu
{ (* TODO *) }.
Record tile_list_obu_type : Set := make_tile_list_obu
{ (* TODO *) }.
Record padding_obu_type : Set := make_padding_obu
{ (* TODO *) }.
Record reserved_obu_type : Set := make_reserved_obu
{ (* TODO *) }.

Definition obu_type_to_payload_type (type : obu_type_enum.t) : Set :=
  match type with
  | obu_type_enum.Reserved_0 => reserved_obu_type
  | obu_type_enum.OBU_SEQUENCE_HEADER => sequence_header_obu_type
  | obu_type_enum.OBU_TEMPORAL_DELIMITER => temporal_delimiter_obu_type
  | obu_type_enum.OBU_FRAME_HEADER => frame_header_obu_type
  | obu_type_enum.OBU_TILE_GROUP => tile_group_obu_type
  | obu_type_enum.OBU_METADATA => metadata_obu_type
  | obu_type_enum.OBU_FRAME => frame_obu_type
  | obu_type_enum.OBU_REDUNDANT_FRAME_HEADER => frame_header_obu_type
  | obu_type_enum.OBU_TILE_LIST => tile_list_obu_type
  | obu_type_enum.Reserved_9 => reserved_obu_type
  | obu_type_enum.Reserved_10 => reserved_obu_type
  | obu_type_enum.Reserved_11 => reserved_obu_type
  | obu_type_enum.Reserved_12 => reserved_obu_type
  | obu_type_enum.Reserved_13 => reserved_obu_type
  | obu_type_enum.Reserved_14 => reserved_obu_type
  | obu_type_enum.OBU_PADDING => padding_obu_type
  end.

Record open_bitstream_unit_type : Set := make_open_bitstream_unit
{
  obu_header : obu_header_type;
  obu_payload : option (obu_type_to_payload_type (obu_type obu_header))
}.
