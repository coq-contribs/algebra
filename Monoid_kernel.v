Set Implicit Arguments.
Unset Strict Implicit.
Require Export Monoid_util.
Require Export Parts2.
Section Image_hom.
Variable M M' : MONOID.
Variable f : Hom M M'.

Definition image_monoid_hom : submonoid M'.
apply (BUILD_SUB_MONOID (G:=M') (H:=image_map f)).
simpl in |- *.
intros x y H' H'0; try assumption.
elim H'0; intros x0 E; elim E; intros H'1 H'2; try exact H'1; clear E H'0.
elim H'; intros x1 E; elim E; intros H'0 H'3; try exact H'0; clear E H'.
exists (sgroup_law M x1 x0); split; [ try assumption | idtac ].
apply
 Trans
  with
    (sgroup_law M' (Ap (sgroup_map (monoid_sgroup_hom f)) x1)
       (Ap (sgroup_map (monoid_sgroup_hom f)) x0)); 
 auto with algebra.
simpl in |- *.
exists (monoid_unit M); split; [ try assumption | idtac ].
auto with algebra.
auto with algebra.
Defined.

Lemma image_monoid_prop : forall x : M, in_part (f x) image_monoid_hom.
simpl in |- *.
intros x; exists x; split; [ try assumption | idtac ]; auto with algebra.
Qed.

Lemma image_monoid_prop_rev :
 forall y : M', in_part y image_monoid_hom -> exists x : M, Equal y (f x).
simpl in |- *.
intros y H'; try assumption.
elim H'; intros x E; elim E; intros H'0 H'1; try exact H'0; clear E H'.
exists x; try assumption.
Qed.
End Image_hom.
Hint Resolve image_monoid_prop image_monoid_prop: algebra.