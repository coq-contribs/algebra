Set Implicit Arguments.
Unset Strict Implicit.
Require Export Zring.
Require Export Fraction_field.
(* Check fraction_cfield. *)

Lemma Z_one_diff_zero : ~ Equal (ring_unit ZZ) (monoid_unit ZZ).
simpl in |- *.
unfold not in |- *; intros.
inversion H.
Qed.

Definition Q := fraction_cfield Z_one_diff_zero Zzero_dec.
