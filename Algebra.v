Set Implicit Arguments.
Unset Strict Implicit.
Require Export Hom_module.
Section algebra_def.
Variable R : CRING.

Record algebra_on (Mod : MODULE R) : Type := 
  {algebra_bilinear_map : Hom_module Mod (Hom_module Mod Mod)}.

Record algebra : Type := 
  {algebra_carrier :> module R; algebra_on_def :> algebra_on algebra_carrier}.
Coercion Build_algebra : algebra_on >-> algebra.

Definition algebra_mult (A : algebra) (x y : A) : A :=
  algebra_bilinear_map A x y.

Record ring_algebra_on (A : algebra) : Type := 
  {ring_algebra_assoc :
    forall x y z : A,
    Equal (algebra_mult (algebra_mult x y) z)
      (algebra_mult x (algebra_mult y z));
   ring_algebra_unit : A;
   ring_algebra_unit_l :
    forall x : A, Equal (algebra_mult ring_algebra_unit x) x;
   ring_algebra_unit_r :
    forall x : A, Equal (algebra_mult x ring_algebra_unit) x}.

Record ring_algebra : Type := 
  {ring_algebra_algebra :> algebra;
   ring_algebra_on_def :> ring_algebra_on ring_algebra_algebra}.
Coercion Build_ring_algebra : ring_algebra_on >-> ring_algebra.
End algebra_def.
