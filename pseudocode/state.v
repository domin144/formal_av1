Require Import ZArith.
Require Import String.
Require Import Ascii.
Require Import Structures.Orders.
Require Import Structures.OrdersEx.
Require Import Lists.List.


Definition lt_not_eq_prop {X : Type} (eq lt : X -> X -> Prop) : Prop :=
  forall (x y : X),
    lt x y -> ~(eq x y).


Module list_as_EqualityType (X : EqualityType) <: EqualityType.

  Definition t := list X.t.

  Inductive eq_dummy : t -> t -> Prop :=
    | eq_nil :
      eq_dummy nil nil
    | eq_more :
      forall h0 h1 t0 t1,
      X.eq h0 h1 -> eq_dummy t0 t1 -> eq_dummy (h0 :: t0) (h1 :: t1).

  Definition eq := eq_dummy.

  Theorem eq_refl : reflexive t eq.
  Proof.
    intros l.
    induction l.
    - apply eq_nil.
    - apply eq_more.
      + apply Equivalence_Reflexive.
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
        * apply Equivalence_Symmetric.
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
      + apply Equivalence_Transitive with h1;
          auto.
      + apply IHH_xy.
        auto.
  Qed.

  Theorem eq_equiv : Equivalence eq.
    split.
    - apply eq_refl.
    - apply eq_sym.
    - apply eq_trans.
  Qed.

End list_as_EqualityType.

Module list_as_DecStrOrder (X : OrderedType) <: DecStrOrder.

  Include list_as_EqualityType X.

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

  Theorem lt_irreflexive : Irreflexive lt.
  Proof.
    unfold Irreflexive.
    unfold Reflexive.
    intros.
    intros Hinv.
    induction x.
    - inversion Hinv.
    - inversion Hinv; subst.
      + apply StrictOrder_Irreflexive with a.
        auto.
      + auto.
  Qed.

  Lemma lt_compat_easy :
    forall x0 x1 y0 y1, X.eq x0 x1 -> X.eq y0 y1 -> (X.lt x0 y0 <-> X.lt x1 y1).
  Proof.
    intros.
    apply X.lt_compat;
      auto.
  Qed.

  Theorem lt_transitive : Transitive lt.
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
        apply StrictOrder_Transitive with h1;
          auto.
      + apply lt_h.
        apply lt_compat_easy with h0 h1.
        * apply Equivalence_Reflexive.
        * apply Equivalence_Symmetric.
          auto.
        * auto.
    - intros.
      destruct z0.
      + inversion H0.
      + inversion H0;
          subst.
        * apply lt_h.
          apply lt_compat_easy with h1 t2;
            auto.
          apply Equivalence_Reflexive.
        * apply lt_t.
          { apply Equivalence_Transitive with h1;
              auto. }
          { apply IHH_xy.
            auto. }
  Qed.

  Theorem lt_strorder : StrictOrder lt.
    split.
    - apply lt_irreflexive.
    - apply lt_transitive.
  Qed.

  Theorem lt_compat_half : 
    forall x0 x1 y0 y1,
      eq x0 y0 -> eq x1 y1 -> lt x0 x1 -> lt y0 y1.
    intros x0.
    induction x0.
    - intros x1 y0 y1 Heq0 Heq1.
      inversion Heq0;
        subst.
      inversion Heq1;
        subst.
      + intro.
        auto.
      + intro.
        apply lt_nil.
    - intros x1 y0 y1 Heq0 Heq1.
      inversion Heq0;
        subst.
      inversion Heq1;
        subst.
      + intro H;
          inversion H.
      + intro Hlt.
        inversion Hlt;
          subst.
          * apply lt_h.
            apply lt_compat_easy with a h0.
            { apply Equivalence_Symmetric.
              auto. }
            { apply Equivalence_Symmetric.
              auto. }
            { auto. }
          * apply lt_t.
            { apply Equivalence_Transitive with a.
              - apply Equivalence_Symmetric.
                auto.
              - apply Equivalence_Transitive with h0;
                  auto. }
            { apply IHx0 with t0;
                auto. }
  Qed.

  Theorem lt_compat : Proper (eq==>eq==>iff) lt.
    intros x0 y0 Heq0 x1 y1 Heq1.
    split.
    - apply lt_compat_half;
        auto.
    - apply lt_compat_half.
      + apply (@Equivalence_Symmetric t eq eq_equiv).
        * auto.
      + apply (@Equivalence_Symmetric t eq eq_equiv).
        * auto.
  Qed.

  Fixpoint compare (x y : t) : comparison :=
    match x, y with
    | nil, nil => Eq
    | nil, _ :: _ => Lt
    | _ :: _, nil => Gt
    | xh :: xt, yh :: yt => match X.compare xh yh with
      | Lt => Lt
      | Gt => Gt
      | Eq => compare xt yt
      end
    end.

  Theorem compare_spec : forall x y, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
    induction x as [| hx tx IH].
    - destruct y.
      + apply CompEq.
        apply eq_nil.
      + apply CompLt.
        apply lt_nil.
    - destruct y as [| hy ty].
      + apply CompGt.
        apply lt_nil.
      + simpl.
        pose proof (X.compare_spec hx hy) as Hhcomp.
        inversion Hhcomp;
          subst.
        * pose proof (IH ty) as IHt.
          inversion IHt;
            subst.
          { apply CompEq.
            apply eq_more;
              auto. }
          { apply CompLt.
            apply lt_t;
              auto. }
          { apply CompGt.
            apply lt_t.
            - apply Equivalence_Symmetric.
              auto.
            - auto. }
        * apply CompLt.
          apply lt_h.
          auto.
        * apply CompGt.
          apply lt_h.
          auto.
  Qed.

End list_as_DecStrOrder.

Module list_as_OrderedType (X : OrderedType) <: OrderedType.
  Module DSO := list_as_DecStrOrder X.
  Include DSO_to_OT DSO.
End list_as_OrderedType.

Module Type mapped_OT (Y : OrderedType).
  Parameter Inline t : Type.

  Parameter Inline f : t -> Y.t.

  Definition eq (x y : t) : Prop :=
    Y.eq (f x) (f y).

  Definition lt (x y : t) : Prop :=
    Y.lt (f x) (f y).
End mapped_OT.

Module mapped_to_DecStrOrder (Y : OrderedType) (M : mapped_OT Y) <: DecStrOrder.

  Definition t := M.t.

  Definition eq := M.eq.

  Definition lt := M.lt.

  Definition f := M.f.

  Theorem eq_refl : reflexive t eq.
  Proof.
    intros x.
    unfold eq.
    unfold M.eq.
    apply Equivalence_Reflexive.
  Qed.

  Theorem eq_sym : symmetric t eq.
  Proof.
    intros x y.
    unfold eq.
    unfold M.eq.
    apply Equivalence_Symmetric.
  Qed.

  Theorem eq_trans : transitive t eq.
  Proof.
    intros x y z.
    unfold eq.
    unfold M.eq.
    apply Equivalence_Transitive.
  Qed.

  Theorem eq_equiv : Equivalence eq.
    split.
    - apply eq_refl.
    - apply eq_sym.
    - apply eq_trans.
  Qed.

  Theorem lt_irreflexive : Irreflexive lt.
    intros x Hinv.
    unfold lt in Hinv.
    unfold M.lt in Hinv.
    apply (StrictOrder_Irreflexive (M.f x)).
    auto.
  Qed.

  Theorem lt_transitive : Transitive lt.
    unfold lt.
    intros x y z Hxy Hyz.
    unfold M.lt.
    apply (StrictOrder_Transitive (M.f x) (M.f y) (M.f z)).
    - auto.
    - auto.
  Qed.

  Theorem lt_strorder : StrictOrder lt.
    split.
    - apply lt_irreflexive.
    - apply lt_transitive.
  Qed.

  Theorem lt_compat : Proper (eq==>eq==>iff) lt.
    intros x0 x1 Heqx y0 y1 Heqy.
    unfold lt.
    unfold M.lt.
    apply Y.lt_compat.
    - auto.
    - auto.
  Qed.

  Definition compare x y := Y.compare (f x) (f y).

  Theorem compare_spec : forall x y, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros x y.
    unfold compare.
    remember (Y.compare_spec (f x) (f y)) as Yc.
    inversion Yc.
    - apply CompEq.
      auto.
    - apply CompLt.
      auto.
    - apply CompGt.
      auto.
  Qed.

End mapped_to_DecStrOrder.

Module mapped_to_OT (Y : OrderedType) (M : mapped_OT Y) <: OrderedType.
  Module DSO := mapped_to_DecStrOrder Y M.
  Include DSO_to_OT DSO.
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
    Module ascii_list_os_OT := list_as_OrderedType ascii_as_OT.
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
(* Reference may olso refer to an array with no or incomplete subscript list.
   For such reference, valid state will always return "None", but the reference
   can be used in subscript expression to form reference with extended subscrpt
   list. Subscript operations can be repeated until the subscript list is
   complete. *)
Inductive reference :=
  | ref_variable : string -> list Z -> reference.

Module reference_as_OT <: OrderedType.
  Module reference_as_OT_local.
    Module list_Z_as_OT := list_as_OrderedType Z_as_OT.
    Module pair_as_OT := PairOrderedType string_as_OT list_Z_as_OT.
    Module as_mapped_OT : mapped_OT pair_as_OT.
      Definition t := reference.
      Definition f (x : t) : pair_as_OT.t :=
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

Definition state := reference -> option Z.

Definition empty_state (ref : reference) : option Z := None.

Example state_ex0 :
  empty_state (ref_variable "terefere" nil) = None.
Proof. reflexivity. Qed.