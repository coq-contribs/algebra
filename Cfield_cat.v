Set Implicit Arguments.
Unset Strict Implicit.
Require Export Ring_cat.
Require Export Field_cat.
(** Title "The category of commutative fields." *)

Record cfield : Type := 
  {cfield_ring : cring; cfield_on_def :> field_on cfield_ring}.
Coercion cfield_ring : cfield >-> cring.

Definition CFIELD := full_subcat (C:=CRING) (C':=cfield) cfield_ring.