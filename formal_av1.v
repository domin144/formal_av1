(*
 * Copyright 2018 Dominik Wójt
 *
 * This file is part of formal_av1.
 *
 * formal_av1 is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * formal_av1 is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with formal_av1.  If not, see <http://www.gnu.org/licenses/>.
 *
 *)

Require Import List ZArith.
Import ListNotations.

Require Import basic_types.
Require Import pseudocodes.
Require Import parser.
Require Import syntax_processor.

Inductive bit := bit_0 | bit_1.
Inductive byte :=
  byte_intro : forall (_ _ _ _ _ _ _ _ : bit), byte.
Definition open_bitstream_unit := list byte.

Section frame_def.
Open Scope Z_scope.
Inductive frame :=
  | frame_intro :
    forall (width height planes : Z),
      (0 < width) -> (0 < height) -> (0 < planes) ->
      (
        forall (x y c : Z),
          (0 <= x < width) -> (0 <= y < height) -> (0 <= c < planes) -> Z) ->
        frame.
End frame_def.

Definition tile := frame.

(* Ordering of OBUs *)

(* Inductive temporal_unit :=
  | temporal_unit_intro :
    temporal_delimiter ->
    list sequence_header ->
    list metadata_obu ->
    (frame_header * list tile_group_obu * list padding_obu) ->
    list (frame_header * list tile_group_obu * list padding_obu) ->
    temporal_unit.
Inductive coded_video_sequence :=
  | coded_video_sequence_intro :
    temporal_unit -> list temporal unit -> coded_video_sequence.
Inductive bitstream :=
  | bistream_intro :
    coded_video_sequece -> list coded_video_sequece -> bitstream. *)

(* The final definitions! *)

Inductive general_decode_relation :
    list open_bitstream_unit -> list frame -> Prop := (* TODO *).

Inductive large_scale_tile_input := (* TODO *).
Inductive large_scale_tile_decode_relation :
    large_scale_tile_input -> list tile -> Prop := (* TODO *).

