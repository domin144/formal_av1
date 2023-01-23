Definition conditional_set (b : bool) (t : Set) : Set :=
  match b with
  | true => t
  | false => unit
  end.

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

Record timing_info_type : Set := make_timing_info
{
  num_units_in_display_tick : nat;
  time_scale : nat;
  equal_picture_interval : bool;
  num_ticks_per_picutre_minus_1 : conditional_set equal_picture_interval nat;
}.

Record decoder_model_info_type : Set := make_decoder_model_info
{
  buffer_delay_length_minus_1 : nat;
  num_units_in_decoding_tick : nat;
  buffer_removal_time_length_minus_1 : nat;
  frame_presentation_time_length_minus_1 : nat;
}.

Record operating_parameters_info_type : Set := make_operating_parameters_info
{
  (* TODO *)
}.

Record sequence_header_obu_type : Set := make_sequence_header_obu
{
  seq_profile : nat;
  still_picture : bool;
  reduced_still_picture_header : bool;
  timing_info_present_flag : bool;
  timing_info : option timing_info_type;
  decoder_model_info_present_flag : bool;
  decoder_model_info : option decoder_model_info_type;
  initial_display_delay_present_flag : bool;
  operating_points_cnt_minus_1 : nat;
  operating_point_idc : list nat;
  seq_level_idx : list nat;
  seq_tier : list bool;
  decoder_model_present_for_this_op : list bool;
  operating_parameters_info : list (option operating_parameters_info_type);
  initial_display_delay_present_for_this_op : list nat;
  initial_display_delay_minus_1 : list (option nat);
  frame_width_bits_minus_1 : nat;
  frame_height_bits_minus_1 : nat;
  max_frame_width_minus_1 : nat;
  max_frame_height_minus_1 : nat;
  frame_id_numbers_present_flag : bool;
  delta_frame_id_lenght_minus_2 : nat;
  additional_frame_id_length_minus_1 : nat;
  (* TODO *)
}.

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
  obu_payload : obu_type_to_payload_type (obu_type obu_header)
}.
