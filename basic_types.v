Require Import ZArith.
Require Fin.
Require Vector.

Inductive frame :=
| frame_intro :
  forall (width height planes : nat),
    Vector.t (Vector.t (Vector.t Z width) height) planes -> frame.

Inductive bit := bit_0 | bit_1.

Module byte.

  Definition bits_count := 8.

  Definition t := Vector.t bit bits_count.

  (* Bit index 0 is the least significant one. *)
  Definition bit_index := Fin.t bits_count.

End byte.

Definition open_bitstream_unit := list byte.t.

Definition bitstream := list open_bitstream_unit.
