Set Implicit Arguments.
Unset Strict Implicit.
Require Export Monoid_cat.
(** Title "The category of groups." *)
Section Inverse.
Variable G : SET.
Variable f : law_of_composition G.
Variable e : G.
Variable inv : MAP G G.

Definition inverse_r := forall x : G, Equal (f (couple x (inv x))) e.

Definition inverse_l := forall x : G, Equal (f (couple (inv x) x)) e.
End Inverse.

Record group_on (G : monoid) : Type := 
  {group_inverse_map : Map G G;
   group_inverse_r_prf :
    inverse_r (sgroup_law_map G) (monoid_unit G) group_inverse_map;
   group_inverse_l_prf :
    inverse_l (sgroup_law_map G) (monoid_unit G) group_inverse_map}.

Record group : Type := 
  {group_monoid :> monoid; group_on_def :> group_on group_monoid}.
Coercion Build_group : group_on >-> group.
Set Strict Implicit.
Unset Implicit Arguments.

Definition group_inverse (G : group) (x : G) := group_inverse_map G x.
Set Implicit Arguments.
Unset Strict Implicit.

Definition GROUP := full_subcat (C:=MONOID) (C':=group) group_monoid.