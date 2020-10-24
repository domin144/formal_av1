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
Require Vector.
Import ListNotations.

Require Import formal_av1.basic_types.
Require Import formal_av1.pseudocodes.
Require Import formal_av1.parser.
Require Import formal_av1.syntax_processor.

Section frame_def.
Open Scope Z_scope.
Inductive frame :=
  | frame_intro :
    forall (width height planes : nat),
      Vector.t (Vector.t (Vector.t Z width) height) planes -> frame.
End frame_def.

Definition tile := frame.

(* The final definitions! *)

Inductive general_decode_relation :
    list open_bitstream_unit -> list frame -> Prop := (* TODO *).

Inductive large_scale_tile_input := (* TODO *).
Inductive large_scale_tile_decode_relation :
    large_scale_tile_input -> list tile -> Prop := (* TODO *).

