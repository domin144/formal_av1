Require Import List ZArith.

Require Import basic_types.

Inductive bitstream_position :=
  bitstream_postion_intro : Z -> Z -> bitstream_position.

Inductive bitstream_at_relation :
    bitstream -> bitstream_position -> bit -> Prop :=
  bitstream_at_relation_intro :
    forall bs byte_index bit_index value,
      False(* TODO *) ->
      bitstream_at_relation bs (bitstream_postion_intro byte_index bit_index)
        value.

(* Inductive read_bit_relation :
    bitstream -> bitstream_position -> bit -> bitstream_position -> Prop :=
  | read_bit_relation_intro :
    forall bs bp0 b bp1,
*)