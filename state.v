Require Import ZArith.
Require Import String.
Require Import Ascii.
Require Import Relations.
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
  Module list_as_MiniOT_X := list_as_MiniOT X.
  Include MOT_to_OT list_as_MiniOT_X.
End list_as_OT.

(* An expression might evaluate to reference to single variable or array element.
   Reference to single variable is label with empty subscrtip list. *)
Inductive reference :=
  | ref_variable : string -> list Z -> reference.

Definition lt_ascii (c0 c1 : ascii) : Prop :=
  N.lt (N_of_ascii c0) (N_of_ascii c1).

Lemma lt_ascii_trans :
  transitive ascii lt_ascii.
Proof.
  intros x y z lt_xy lt_yz.
  apply N.lt_trans with (m := N_of_ascii y); auto.
Qed.

Lemma lt_ascii_not_eq :
  lt_not_eq_prop eq lt_ascii.
Proof.
  intros x y H Hinv.
  subst.
  unfold lt_ascii in H.
  apply N.lt_irrefl with (N_of_ascii y).
  auto.
Qed.

Definition compare_ascii (c0 c1 : ascii) : Compare lt_ascii (@eq ascii) c0 c1.
Proof.
  destruct (N_as_OT.compare (N_of_ascii c0) (N_of_ascii c1)).
  - apply LT.
    apply l.
  - apply EQ.
    unfold N_as_OT.eq in e.
    rewrite <- ascii_N_embedding.
    rewrite <- e.
    rewrite ascii_N_embedding.
    reflexivity.
  - apply GT.
    apply l.
Defined.

Inductive lt_string : string -> string -> Prop :=
  | lt_string_empty :
    forall c s, lt_string EmptyString (String c s)
  | lt_string_x :
    forall c0 c1 s0 s1,
      lt_ascii c0 c1 -> lt_string (String c0 s0) (String c1 s1)
  | lt_string_l :
    forall c s0 s1,
      lt_string s0 s1 -> lt_string (String c s0) (String c s1).

Lemma lt_string_trans :
  transitive string lt_string.
Proof.
  intros x y z H_xy.
  generalize z.
  induction H_xy.
  - intros z0 H_yz.
    inversion H_yz;
      apply lt_string_empty.
  - intros z0 H_yz.
    inversion H_yz; subst.
    + apply lt_string_x.
      apply lt_ascii_trans with c1;
        auto.
    + apply lt_string_x; auto.
  - intros z0 H_yz.
    inversion H_yz; subst.
    + apply lt_string_x;
        auto.
    + apply lt_string_l.
      apply IHH_xy.
      auto.
Qed.

Lemma lt_string_not_eq :
  lt_not_eq_prop eq lt_string.
Proof.
  intros x y H.
  induction H.
  - intros Hinv.
    inversion Hinv.
  - intros Hinv.
    inversion Hinv; subst.
    apply lt_ascii_not_eq in H.
    apply H.
    reflexivity.
  - intros Hinv.
    inversion Hinv; subst.
    apply IHlt_string.
    reflexivity.
Qed.

Fixpoint compare_string (l0 l1 : string) :
  Compare lt_string (@eq string) l0 l1.
Proof.
  destruct l0 as [| h0 t0].
  - destruct l1 as [| h1 t1].
    + apply EQ.
      reflexivity.
    + apply LT.
      apply lt_string_empty.
  - destruct l1 as [| h1 t1].
    + apply GT.
      apply lt_string_empty.
    + destruct (compare_ascii h0 h1).
      * apply LT.
        apply lt_string_x.
        auto.
      * subst.
        destruct (compare_string t0 t1).
        { apply LT.
          apply lt_string_l.
          auto. }
        { apply EQ.
          subst.
          reflexivity. }
        { apply GT.
          apply lt_string_l.
          auto. }
      * apply GT.
        apply lt_string_x.
        auto.
Defined.

Module list_Z_as_OT := list_as_OT Z_as_OT.

Inductive lt_reference : reference -> reference -> Prop :=
  | lt_reference_string :
    forall s0 s1 l0 l1,
      lt_string s0 s1 -> lt_reference (ref_variable s0 l0) (ref_variable s1 l1)
  | lt_reference_list :
    forall s l0 l1,
      list_Z_as_OT.lt l0 l1 -> lt_reference (ref_variable s l0) (ref_variable s l1).

Theorem lt_reference_trans :
  transitive reference lt_reference.
Proof.
  intros x y z H_xy H_yz.
  destruct H_xy as [xs ys xl yl H_xy | s xl yl H_xy].
  - destruct z as [zs zl].
    apply lt_reference_string.
    inversion H_yz as [ys0 zs0 yl0 zl0 H_yz0 | s2 yl0 zl0 H_yz0]; subst.
    + apply lt_string_trans with ys;
        auto.
    + auto.
  - inversion H_yz as [ys zs yl0 zl H_yz0 | s2 yl0 zl H_yz0]; subst.
    + apply lt_reference_string.
      auto.
    + apply lt_reference_list.
      apply list_Z_as_OT.lt_trans with yl;
        auto.
Qed.

Theorem lt_reference_not_eq :
  lt_not_eq_prop eq lt_reference.
Proof.
  unfold lt_not_eq_prop.
  intros.
  inversion H; subst.
  - intros Hinv.
    inversion Hinv; subst.
    apply lt_string_not_eq in H0.
    auto.
  - intros Hinv.
    inversion Hinv; subst.
    apply list_Z_as_OT.lt_not_eq in H0.
    * apply H0.
      apply list_Z_as_OT.eq_refl.
Qed.

Module ascii_as_OT <: UsualOrderedType.
  Definition t := ascii.
  Definition eq := @eq t.
  Definition lt := lt_ascii.
  Definition eq_refl := @eq_refl ascii.
  Definition eq_sym := @eq_sym ascii.
  Definition eq_trans := @eq_trans ascii.
  Definition lt_trans := lt_ascii_trans.
  Definition lt_not_eq := lt_ascii_not_eq.
  Definition compare x y := compare_ascii x y.
  Definition eq_dec := ascii_dec.
End ascii_as_OT.

Module string_as_OT <: UsualOrderedType.
  Definition t := string.
  Definition eq := @eq string.
  Definition lt := lt_string.
  Definition eq_refl := @eq_refl string.
  Definition eq_sym := @eq_sym string.
  Definition eq_trans := @eq_trans string.
  Definition lt_trans := lt_string_trans.
  Definition lt_not_eq := lt_string_not_eq.
  Definition compare x y := compare_string x y.
  Definition eq_dec := string_dec.
End string_as_OT.

Module reference_as_OT <: UsualOrderedType.
  Definition t := reference.
  Definition eq := @eq reference.
  Definition lt := lt_reference.
  Definition eq_refl := @eq_refl reference.
  Definition eq_sym := @eq_sym reference.
  Definition eq_trans := @eq_trans reference.
  Definition lt_trans := lt_reference_trans.
  Definition lt_not_eq := lt_reference_not_eq.
  Definition compare (ref_variable xs xl) (ref_variable ys yl) :=
    match (
End reference_as_OT.