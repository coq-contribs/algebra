Set Implicit Arguments.
Unset Strict Implicit.
Require Export Monoid_cat.
(** Title "The monoid of maps of a set into itself." *)
Section Def.
Variable E : SET.

Definition endo_comp : law_of_composition (Hom E E).
unfold law_of_composition in |- *.
apply
 (Build_Map
    (Ap:=fun x : cart (Hom E E) (Hom E E) => comp_map_map (proj1 x) (proj2 x))).
red in |- *.
auto with algebra.
Defined.

Definition Endo_SET_sgroup : SGROUP.
apply (Build_sgroup (sgroup_set:=Hom E E)).
apply (Build_sgroup_on (E:=Hom E E) (sgroup_law_map:=endo_comp)).
red in |- *.
simpl in |- *.
unfold Map_eq in |- *; auto with algebra.
Defined.

Definition Endo_SET : MONOID.
apply (Build_monoid (monoid_sgroup:=Endo_SET_sgroup)).
apply (Build_monoid_on (A:=Endo_SET_sgroup) (monoid_unit:=Id E)).
red in |- *.
simpl in |- *.
unfold Map_eq in |- *; auto with algebra.
red in |- *.
simpl in |- *.
unfold Map_eq in |- *; auto with algebra.
Defined.
End Def.