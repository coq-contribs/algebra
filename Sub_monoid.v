Set Implicit Arguments.
Unset Strict Implicit.
Require Export Sub_sgroup.
Require Export Monoid_facts.
Section Def.
Variable G : MONOID.
Section Sub_monoid.
Variable H : subsgroup G.
Hypothesis Hunit : in_part (monoid_unit G) H.

Definition submonoid_monoid : monoid.
apply (Build_monoid (monoid_sgroup:=H)).
apply (Build_monoid_on (A:=H) (monoid_unit:=Build_subtype Hunit)).
red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
Defined.
End Sub_monoid.

Record submonoid : Type := 
  {submonoid_subsgroup : subsgroup G;
   submonoid_prop : in_part (monoid_unit G) submonoid_subsgroup}.

Definition monoid_of_submonoid (H : submonoid) :=
  submonoid_monoid (submonoid_prop H).
End Def.
Coercion monoid_of_submonoid : submonoid >-> monoid.
Coercion submonoid_subsgroup : submonoid >-> subsgroup.
Section Injection.
Variable G : MONOID.
Variable H : submonoid G.

Lemma submonoid_in_prop : in_part (monoid_unit G) H.
apply (submonoid_prop (G:=G) H); auto with algebra.
Qed.

Definition inj_submonoid : Hom (H:MONOID) G.
apply (Build_monoid_hom (E:=H) (F:=G) (monoid_sgroup_hom:=inj_subsgroup H)).
red in |- *.
auto with algebra.
Defined.

Lemma inj_subsmonoid_injective : injective inj_submonoid.
red in |- *.
auto with algebra.
Qed.
End Injection.
Hint Resolve submonoid_in_prop inj_subsmonoid_injective: algebra.
