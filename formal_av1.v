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

Module Syntax_processor.

Definition definitionsE :=
  (map Parser.parse_pseudocode syntax_pseudocodes).

Compute definitionsE.

(* Theorem all_definitions_parsed :
  forallb
    (
      fun x => match x with
      | Parser.SomeE (_, []) => true
      | _ => false
      end)
    definitionsE = true.
Proof. *)
(* TODO *)


Definition state := Parser.token -> Z.

Reserved Notation "e '\\' n" (at level 50, left associativity).

End Syntax_processor.

Inductive bit := bit_0 | bit_1.
Inductive byte :=
  byte_intro : forall (_ _ _ _ _ _ _ _ : bit), byte.
Definition bytestream := list byte.
