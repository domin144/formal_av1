Require Import ZArith.
Require Import String.
Require Import Ascii.
Require Import Relations.
Require Import Equalities.
Require Import OrderedType.
Require Import OrderedTypeEx.

Definition lt_not_eq_prop {X : Type} (eq lt : X -> X -> Prop) : Prop :=
  forall (x y : X),
    lt x y -> ~(eq x y).

Module list_as_MiniOT (X : OrderedType) <: MiniOrderedType.

  Definition t := list X.t.

  Inductive eq_dummy : t -> t -> Prop :=
    | eq_nil :
      eq_dummy nil nil
    | eq_more :
      forall h0 h1 t0 t1,
      X.eq h0 h1 -> eq_dummy t0 t1 -> eq_dummy (h0 :: t0) (h1 :: t1).

  Definition eq := eq_dummy.

  Inductive lt_dummy : t -> t -> Prop :=
    | lt_nil :
      forall h t,
        lt_dummy nil (h :: t)
    | lt_h :
      forall h0 h1 t0 t1,
        X.lt h0 h1 -> lt_dummy (h0 :: t0) (h1 :: t1)
    | lt_t :
      forall h0 h1 t0 t1,
        X.eq h0 h1 -> lt_dummy t0 t1 -> lt_dummy (h0 :: t0) (h1 :: t1).

  Definition lt := lt_dummy.

  Theorem eq_refl : reflexive t eq.
  Proof.
    intros l.
    induction l.
    - apply eq_nil.
    - apply eq_more.
      + apply X.eq_refl.
      + apply IHl.
  Qed.

  Theorem eq_sym : symmetric t eq.
  Proof.
    intros l.
    induction l.
    - intros x Hx.
      inversion Hx.
      apply eq_refl.
    - intros y Hy.
      destruct y.
      + inversion Hy.
      + inversion Hy;
          subst.
        apply eq_more.
        * apply X.eq_sym.
          auto.
        * apply IHl.
          auto.
  Qed.

  Definition eq_trans : transitive t eq.
  Proof.
    intros x y z H_xy.
    generalize z.
    induction H_xy.
    - intros z0 H_yz.
      auto.
    - intros z0 H_yz.
      inversion H_yz;
        subst.
      apply eq_more.
      + apply X.eq_trans with h1;
          auto.
      + apply IHH_xy.
        auto.
  Qed.

  Theorem lt_trans : transitive t lt.
  Proof.
    intros x y z H_xy.
    generalize z.
    induction H_xy.
    - intros z0 H_yz.
      inversion H_yz;
        apply lt_nil.
    - intros z0 H_yz.
      inversion H_yz;
        subst.
      + apply lt_h.
        apply X.lt_trans with h1;
          auto.
      + apply lt_h.
        (* TODO: replace this part with some ready proof on X *)
        destruct (X.compare h0 h3).
        * auto.
        * exfalso.
          apply X.lt_not_eq with h0 h1; 
            auto.
          apply X.eq_trans with h3;
            auto.
        * exfalso.
          apply X.lt_not_eq with h3 h1;
            auto.
          apply X.lt_trans with h0;
            auto.
    - intros z0 H_yz.
      inversion H_yz;
        subst.
      + apply lt_h.
        destruct (X.compare h0 h3).
        * auto.
        * exfalso.
          apply X.lt_not_eq with h1 h3;
            auto.
          apply X.eq_trans with h0;
            auto.
        * exfalso.
          apply X.lt_not_eq with h1 h0;
            auto.
          apply X.lt_trans with h3;
            auto.
      + apply lt_t.
        * apply X.eq_trans with h1;
            auto.
        * apply IHH_xy.
          auto.
  Qed.

  Theorem lt_not_eq : lt_not_eq_prop eq lt.
  Proof.
    intros x y Hlt Heq.
    induction Hlt;
      subst.
    - inversion Heq.
    - inversion Heq;
        subst.
      apply X.lt_not_eq with h0 h1;
        auto.
    - inversion Heq;
        subst.
      auto.
  Qed.

  Definition compare l0 l1 : Compare lt eq l0 l1.
  Proof.
    generalize l1.
    induction l0 as [| h0 t0].
    - intros l2.
      destruct l2 as [| h1 t1].
      + apply EQ.
        apply eq_refl.
      + apply LT.
        apply lt_nil.
    - intros l2.
      destruct l2 as [| h1 t1].
      + apply GT.
        apply lt_nil.
      + destruct (X.compare h0 h1).
        * apply LT.
          apply lt_h.
          auto.
        * destruct IHt0 with t1.
          { apply LT.
            apply lt_t;
              auto. }
          { apply EQ.
            apply eq_more;
              auto. }
          { apply GT.
            apply lt_t;
              auto. }
        * apply GT.
          apply lt_h.
          auto.
  Qed.
End list_as_MiniOT.

Module list_as_OT (X : OrderedType) <: OrderedType.
  Module list_as_OT_local.
    Module as_MOT := list_as_MiniOT X.
    Module as_OT := MOT_to_OT as_MOT.
  End list_as_OT_local.
  Include list_as_OT_local.as_OT.
End list_as_OT.

Module Type mapped_OT (Y : OrderedType).
  Parameter Inline t : Type.

  Parameter Inline f : t -> Y.t.

  Definition eq (x y : t) : Prop :=
    Y.eq (f x) (f y).

  Definition lt (x y : t) : Prop :=
    Y.lt (f x) (f y).
End mapped_OT.

Module mapped_to_MOT (Y : OrderedType) (M : mapped_OT Y) <: MiniOrderedType.

  Definition t := M.t.

  Definition eq := M.eq.

  Definition lt := M.lt.

  Definition f := M.f.

  Theorem eq_refl : reflexive t eq.
  Proof.
    intros x.
    unfold eq.
    apply Y.eq_refl.
  Qed.

  Theorem eq_sym : symmetric t eq.
  Proof.
    intros x y.
    unfold eq.
    apply Y.eq_sym.
  Qed.

  Theorem eq_trans : transitive t eq.
  Proof.
    intros x y z.
    unfold eq.
    apply Y.eq_trans.
  Qed.

  Theorem lt_trans : transitive t lt.
  Proof.
    intros x y z.
    apply Y.lt_trans.
  Qed.

  Theorem lt_not_eq : lt_not_eq_prop eq lt.
  Proof.
    intros x y.
    apply Y.lt_not_eq.
  Qed.

  Definition compare x y : Compare lt eq x y.
  Proof.
    destruct (Y.compare (f x) (f y)).
    - apply LT.
      auto.
    - apply EQ.
      auto.
    - apply GT.
      auto.
  Qed.

End mapped_to_MOT.

Module mapped_to_OT (Y : OrderedType) (M : mapped_OT Y) <: OrderedType.
  Module mapped_to_OT_local.
    Module as_MOT := mapped_to_MOT Y M.
    Module as_OT := MOT_to_OT as_MOT.
  End mapped_to_OT_local.
  Include mapped_to_OT_local.as_OT.
End mapped_to_OT.

Module ascii_as_OT <: OrderedType.
  Module ascii_as_OT_local.
    Module as_mapped_OT <: mapped_OT N_as_OT.
      Definition t := ascii.
      Definition f := N_of_ascii.
      Definition eq (x y : t) : Prop :=
        N_as_OT.eq (f x) (f y).
      Definition lt (x y : t) : Prop :=
        N_as_OT.lt (f x) (f y).
    End as_mapped_OT.
    Module as_OT := mapped_to_OT N_as_OT as_mapped_OT.
    End ascii_as_OT_local.
  Include ascii_as_OT_local.as_OT.
End ascii_as_OT.

Module string_as_OT <: OrderedType.
  Module string_as_OT_local.
    Module ascii_list_os_OT := list_as_OT ascii_as_OT.
    Module as_mapped_OT <: mapped_OT ascii_list_os_OT.
      Definition t := string.
      Fixpoint f (s : string) : ascii_list_os_OT.t :=
        match s with
        | EmptyString => nil
        | String a s' => a :: f s'
        end.
      Definition eq (x y : t) : Prop :=
        ascii_list_os_OT.eq (f x) (f y).
      Definition lt (x y : t) : Prop :=
        ascii_list_os_OT.lt (f x) (f y).
    End as_mapped_OT.
    Module as_OT := mapped_to_OT ascii_list_os_OT as_mapped_OT.
  End string_as_OT_local.
  Include string_as_OT_local.as_OT.
End string_as_OT.

(* An expression might evaluate to reference to single variable or array element.
   Reference to single variable is label with empty subscrtip list. *)
Inductive reference :=
  | ref_variable : string -> list Z -> reference.

Module reference_as_OT <: OrderedType.
  Module reference_as_OT_local.
    Module list_Z_as_OT := list_as_OT Z_as_OT.
    Module pair_as_OT := PairOrderedType string_as_OT list_Z_as_OT.
    Module as_mapped_OT : mapped_OT pair_as_OT.
      Definition t := reference.
      Fixpoint f (x : t) : pair_as_OT.t :=
        match x with
        | ref_variable s l => (s, l)
        end.
      Definition eq (x y : t) : Prop :=
        pair_as_OT.eq (f x) (f y).
      Definition lt (x y : t) : Prop :=
        pair_as_OT.lt (f x) (f y).
    End as_mapped_OT.
    Module as_OT := mapped_to_OT pair_as_OT as_mapped_OT.
  End reference_as_OT_local.
  Include reference_as_OT_local.as_OT.
End reference_as_OT.
