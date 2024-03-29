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

Require Import formal_av1.basic_types.
Require Import formal_av1.pseudocode.pseudocodes.
Require Import formal_av1.pseudocode.parser.
Require Import formal_av1.pseudocode.processor.

Definition tile := frame.

(* The final definitions! *)

Inductive general_decode_relation :
    list open_bitstream_unit -> list frame -> Prop := (* TODO *).

Inductive large_scale_tile_input := (* TODO *).
Inductive large_scale_tile_decode_relation :
    large_scale_tile_input -> list tile -> Prop := (* TODO *).
