Set Implicit Arguments.
Unset Strict Implicit.
Require Export Zring.
Section Int_power.
Variable G : GROUP.
Set Strict Implicit.
Unset Implicit Arguments.

Definition group_square (x : G) : G := sgroup_law G x x.
Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint group_power_pos (g : G) (p : positive) {struct p} : G :=
  match p with
  | xH => g
  | xO p' => group_square (group_power_pos g p')
  | xI p' => sgroup_law G (group_square (group_power_pos g p')) g
  end.
Set Strict Implicit.
Unset Implicit Arguments.

Definition group_power (g : G) (z : ZZ) : G :=
  match z with
  | Z0 => monoid_unit G
  | Zpos p => group_power_pos g p
  | Zneg p => group_power_pos (group_inverse G g) p
  end.
Set Implicit Arguments.
Unset Strict Implicit.
End Int_power.
Section Lemmas.
Variable G : GROUP.

Lemma group_power_zero :
 forall g : G, Equal (group_power G g (monoid_unit ZZ)) (monoid_unit G).
intros g; simpl in |- *; auto with algebra.
Qed.

Parameter
  group_power_S :
    forall (g : G) (n : ZZ),
    Equal (group_power G g (sgroup_law ZZ n (ring_unit ZZ)))
      (sgroup_law G (group_power G g n) g).
End Lemmas.
Hint Resolve group_power_zero group_power_S: algebra.