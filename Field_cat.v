Set Implicit Arguments.
Unset Strict Implicit.
Require Export Ring_cat.
(** Title "The category of fields." *)

Record field_on (R : ring) : Type := 
  {field_inverse_map : Map R R;
   field_inverse_r_prf :
    forall x : R,
    ~ Equal x (monoid_unit R) ->
    Equal (ring_mult x (Ap field_inverse_map x)) (ring_unit R);
   field_inverse_l_prf :
    forall x : R,
    ~ Equal x (monoid_unit R) ->
    Equal (ring_mult (Ap field_inverse_map x) x) (ring_unit R);
   field_unit_non_zero : ~ Equal (ring_unit R) (monoid_unit R):Prop}.

Record field : Type := 
  {field_ring :> ring; field_on_def :> field_on field_ring}.
Coercion Build_field : field_on >-> field.

Definition FIELD := full_subcat (C:=RING) (C':=field) field_ring.
