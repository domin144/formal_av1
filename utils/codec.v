Require Import Structures.Equalities.

Module Type Codec (X Y : EqualityType).
  (* X is set of not coded, Y is set of coded *)
  Parameter codec : Y.t -> X.t -> Prop.
End Codec.

Module CodecDefs (X Y : EqualityType) (C : Codec X Y).

  Import C.

  Inductive valid_decoder (decoder : Y.t -> X.t) : Prop :=
  | valid_decoder_intro :
    (forall y x, codec y x -> decoder y = x) ->
    valid_decoder decoder.

  Inductive validating_decoder (decoder : Y.t -> option X.t) : Prop :=
  | validating_decoder_intro :
    (forall y x, codec y x <-> decoder y = Some x) ->
    validating_decoder decoder.

  Inductive valid_encoder (encoder : X.t -> Y.t) : Prop :=
  | valid_encoder_intro :
    (forall x, codec (encoder x) x) ->
    valid_encoder encoder.

End CodecDefs.

Module Type LossyCodec (X Y : EqualityType).

  Include Codec X Y.

  Parameter unambiguous :
    forall y x0 x1,
    codec y x0 ->
    codec y x1 ->
    x0 = x1.

End LossyCodec.

Module Type LosslessCodec (X Y : EqualityType).

  Include LossyCodec X Y.

  Parameter complete :
    forall x,
    exists y,
    codec y x.

End LosslessCodec.

Module Type CodecWithDecoderHelper (X Y : EqualityType) (Import C : Codec X Y).

  Module CD := CodecDefs X Y C.
  Import CD.

  Parameter decoder : Y.t -> X.t.

  Parameter decoder_is_valid : valid_decoder decoder.

End CodecWithDecoderHelper.

Module Type CodecWithDecoder (X Y : EqualityType) :=
  (Codec X Y)
  <+ (CodecWithDecoderHelper X Y).

Module CodecWithDecoderToLossy (X Y : EqualityType) (C : CodecWithDecoder X Y)
    <: (LossyCodec X Y).

  Definition codec := C.codec.

  Theorem unambiguous :
    forall y x0 x1,
    codec y x0 ->
    codec y x1 ->
    x0 = x1.
  Proof.
    intros.
    assert (C.decoder y = x0).
      apply C.decoder_is_valid.
      auto.
    assert (C.decoder y = x1).
      apply C.decoder_is_valid.
      auto.
    subst.
    reflexivity.
  Qed.

End CodecWithDecoderToLossy.

Module Type CodecWithEncoderHelper (X Y : EqualityType)
    (Import C : CodecWithDecoder X Y).

  Import CD.

  Parameter encoder : X.t -> Y.t.

  Parameter encoder_is_valid : valid_encoder encoder.

End CodecWithEncoderHelper.

Module Type CodecWithEncoder (X Y : EqualityType) :=
    (CodecWithDecoder X Y)
    <+ (CodecWithEncoderHelper X Y).

Module CodecWithEncoderToLossless
    (X Y : EqualityType)
    (C : CodecWithEncoder X Y)
    <: (LosslessCodec X Y).

  Include CodecWithDecoderToLossy X Y C.

  Theorem complete :
      forall x,
      exists y,
      codec y x.
  Proof.
    intros.
    exists (C.encoder x).
    apply C.encoder_is_valid.
  Qed.

End CodecWithEncoderToLossless.
