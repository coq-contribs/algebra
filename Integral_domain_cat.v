Set Implicit Arguments.
Unset Strict Implicit.
Require Export Ring_cat.
(** Title "The category of integral domains." *)
Section Objects.

Definition idomain_prop (R : CRING) :=
  forall x y : R,
  ~ Equal x (monoid_unit R) ->
  ~ Equal y (monoid_unit R) -> ~ Equal (ring_mult x y) (monoid_unit R).

Record idomain_on (R : cring) : Type :=  {idomain_prf : idomain_prop R}.

Record idomain : Type := 
  {idomain_ring :> cring; idomain_on_def :> idomain_on idomain_ring}.
Coercion Build_idomain : idomain_on >-> idomain.

Definition INTEGRAL_DOMAIN :=
  full_subcat (C:=CRING) (C':=idomain) idomain_ring.
End Objects.