Set Implicit Arguments.
Unset Strict Implicit.
Require Export Monoid_cat.
Section Lemmas.
Variable E : MONOID.

Lemma MONOID_unit_r : forall x : E, Equal (sgroup_law _ x (monoid_unit E)) x.
intros; apply (monoid_unit_r_prf E x).
Qed.

Lemma MONOID_unit_l : forall x : E, Equal (sgroup_law _ (monoid_unit E) x) x.
intros; apply (monoid_unit_l_prf E x).
Qed.

Lemma MONOID_unit_unique :
 forall e : E,
 (forall x : E, Equal (sgroup_law _ x e) x) ->
 (forall x : E, Equal (sgroup_law _ e x) x) -> Equal e (monoid_unit E).
intros e H' H'0; try assumption.
apply Trans with (sgroup_law _ e (monoid_unit E)); auto with algebra.
apply Sym.
apply MONOID_unit_r.
Qed.
Variable F : MONOID.
Variable f : Hom E F.

Lemma MONOID_hom_prop : Equal (f (monoid_unit E)) (monoid_unit F).
apply (monoid_hom_prf f).
Qed.
End Lemmas.
Hint Resolve MONOID_unit_r MONOID_unit_l MONOID_unit_unique MONOID_hom_prop:
  algebra.