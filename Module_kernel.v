Set Implicit Arguments.
Unset Strict Implicit.
Require Export Module_util.
Require Export Sub_module.
Require Export Group_kernel.
(** Title "Kernel and image of a module homomorphism." *)
Section Def.
Variable R : RING.
Variable Mod Mod2 : MODULE R.
Variable f : Hom Mod Mod2.

Definition Ker : submodule Mod.
apply (Build_submodule (R:=R) (M:=Mod) (submodule_subgroup:=Ker f)).
simpl in |- *.
intros a x H'; try assumption.
apply Trans with (module_mult a (f x)); auto with algebra.
apply Trans with (module_mult a (monoid_unit (module_carrier Mod2)));
 auto with algebra.
Defined.

Definition coKer : submodule Mod2.
apply (Build_submodule (R:=R) (M:=Mod2) (submodule_subgroup:=coKer f)).
simpl in |- *.
intros a x H'; try assumption.
elim H'; intros x0 E; elim E; intros H'0 H'1; try exact H'1; clear E H'.
exists (module_mult a x0); split; [ try assumption | idtac ].
apply Trans with (module_mult a (f x0)); auto with algebra.
Defined.

Lemma Ker_prop :
 forall x : Mod, in_part x Ker -> Equal (f x) (monoid_unit Mod2).
auto with algebra.
Qed.

Lemma Ker_prop_rev :
 forall x : Mod, Equal (f x) (monoid_unit Mod2) -> in_part x Ker.
auto with algebra.
Qed.

Lemma coKer_prop : forall x : Mod, in_part (f x) coKer.
simpl in |- *.
intros x; exists x; split; [ idtac | try assumption ]; auto with algebra.
Qed.
End Def.
Hint Resolve Ker_prop coKer_prop: algebra.
