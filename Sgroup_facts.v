Set Implicit Arguments.
Unset Strict Implicit.
Require Export Sgroup_cat.
Section Lemmas.
Variable E : SGROUP.

Lemma SGROUP_assoc :
 forall x y z : E,
 Equal (sgroup_law _ (sgroup_law _ x y) z)
   (sgroup_law _ x (sgroup_law _ y z)).
intros x y z; try assumption.
apply (sgroup_assoc_prf E x y z); auto with algebra.
Qed.

Lemma SGROUP_comp :
 forall x x' y y' : E,
 Equal x x' -> Equal y y' -> Equal (sgroup_law _ x y) (sgroup_law _ x' y').
unfold sgroup_law in |- *; auto with algebra.
Qed.
Variable F : SGROUP.
Variable f : Hom E F.

Lemma SGROUP_hom_prop :
 forall x y : E, Equal (f (sgroup_law _ x y)) (sgroup_law _ (f x) (f y)).
intros x y; try assumption.
apply (sgroup_hom_prf f).
Qed.
End Lemmas.
Hint Resolve SGROUP_assoc SGROUP_comp SGROUP_hom_prop: algebra.