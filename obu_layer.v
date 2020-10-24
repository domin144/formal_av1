Require Import Lists.List.
Import ListNotations.

Require Import formal_av1.basic_types.

Module obu_layer.

(* Ordering of OBUs *)

Inductive temporal_delimiter := (* TODO *).

Inductive obu_codes_temporal_delimiter : open_bitstream_unit -> temporal_delimiter -> Prop :=
  (* TODO *).

Inductive sequence_header := (* TODO *).

Inductive obu_codes_sequence_header : open_bitstream_unit -> sequence_header -> Prop :=
  (* TODO *).

Inductive metadata_obu := (* TODO *).

Inductive obu_codes_metadata_obu : open_bitstream_unit -> metadata_obu -> Prop :=
  (* TODO *).
  
Inductive frame_header := (* TODO *).

Inductive obu_codes_frame_header : open_bitstream_unit -> frame_header -> Prop :=
  (* TODO *).
  
Inductive tile_group_obu := (* TODO *).

Inductive obu_codes_tile_group_obu : open_bitstream_unit -> tile_group_obu -> Prop :=
  (* TODO *).
  
Inductive padding_obu := (* TODO *).

Inductive obu_codes_padding_obu : open_bitstream_unit -> padding_obu -> Prop :=
  (* TODO *).

Inductive temporal_unit :=
  | temporal_unit_intro :
    temporal_delimiter ->
    list sequence_header ->
    list metadata_obu ->
    list (frame_header * list tile_group_obu * list padding_obu) ->
    temporal_unit.

Inductive obu_list_codes_tu : list open_bitstream_unit -> temporal_unit -> Prop :=
  | obu_list_codes_tu_intro :
    forall td td_obu lsh lsh_obu lmeta lmeta_obu lf lf_obu,
      obu_codes_temporal_delimiter td_obu td ->
      Forall2 obu_codes_sequence_header lsh_obu lsh ->
      Forall2 obu_codes_metadata_obu lmeta_obu lmeta ->
      (* TODO: lf_obu lf *)
      obu_list_codes_tu 
        ([td_obu] ++ lsh_obu ++ lmeta_obu ++ lf_obu)
        (temporal_unit_intro td lsh lmeta lf).

Inductive tu_can_start_cvs :
    temporal_unit -> Prop := (* *).

Inductive coded_video_sequence :=
  | coded_video_sequence_intro :
    list temporal_unit -> coded_video_sequence.

Inductive tu_list_codes_cvs : (list temporal_unit) -> coded_video_sequence -> Prop :=
  | tu_list_codes_cvs_intro :
    forall (tu : temporal_unit) (tu_list : list temporal_unit),
      tu_can_start_cvs tu ->
        Forall (fun x => ~(tu_can_start_cvs x)) tu_list ->
          tu_list_codes_cvs (tu :: tu_list) (coded_video_sequence_intro (tu :: tu_list)).

Inductive obu_list_codes_cvs : (list open_bitstream_unit) -> coded_video_sequence -> Prop :=
  | obu_list_codes_cvs_intro :
    forall llobu ltu cvs,
      Forall2 obu_list_codes_tu llobu ltu ->
        tu_list_codes_cvs ltu cvs ->
          obu_list_codes_cvs (concat llobu) cvs.

Inductive bitstream :=
  | bitstream_intro :
    list coded_video_sequence -> bitstream.

Inductive obu_list_codes_bitstream :
    list open_bitstream_unit -> bitstream -> Prop :=
  | obu_list_codes_bitstream_intro :
    forall llobu lcvs,
      Forall2 obu_list_codes_cvs llobu lcvs ->
        length lcvs >= 1 ->
          obu_list_codes_bitstream (concat llobu) (bitstream_intro lcvs).

End obu_layer.
