Set Implicit Arguments.
Unset Strict Implicit.
Require Export Sgroup_cat.
(** Title "The category of monoids." *)
Section Unit.
Variable E : SET.
Variable f : law_of_composition E.
Variable e : E.

Definition unit_r := forall x : E, Equal (f (couple x e)) x.

Definition unit_l := forall x : E, Equal (f (couple e x)) x.
End Unit.

Record monoid_on (A : sgroup) : Type := 
  {monoid_unit : A;
   monoid_unit_r_prf : unit_r (sgroup_law_map A) monoid_unit;
   monoid_unit_l_prf : unit_l (sgroup_law_map A) monoid_unit}.

Record monoid : Type := 
  {monoid_sgroup :> sgroup; monoid_on_def :> monoid_on monoid_sgroup}.
Coercion Build_monoid : monoid_on >-> monoid.
Section Hom.
Variable E F : monoid.

Definition monoid_hom_prop (f : E -> F) :=
  Equal (f (monoid_unit E)) (monoid_unit F).

Record monoid_hom : Type := 
  {monoid_sgroup_hom :> sgroup_hom E F;
   monoid_hom_prf : monoid_hom_prop monoid_sgroup_hom}.
End Hom.

Definition monoid_hom_comp :
  forall E F G : monoid, monoid_hom F G -> monoid_hom E F -> monoid_hom E G.
intros E F G g f; try assumption.
apply
 (Build_monoid_hom (E:=E) (F:=G) (monoid_sgroup_hom:=sgroup_hom_comp g f)).
unfold monoid_hom_prop in |- *; auto with algebra.
simpl in |- *.
unfold comp_map_fun in |- *.
apply Trans with (Ap (sgroup_map g) (monoid_unit F)); auto with algebra.
cut
 (Equal (Ap (sgroup_map (monoid_sgroup_hom f)) (monoid_unit E))
    (monoid_unit F)).
auto with algebra.
apply (monoid_hom_prf f).
apply (monoid_hom_prf g).
Defined.

Definition monoid_id : forall E : monoid, monoid_hom E E.
intros E; try assumption.
apply (Build_monoid_hom (monoid_sgroup_hom:=sgroup_id E)).
red in |- *.
simpl in |- *; auto with algebra.
Defined.

Definition MONOID : category.
apply
 (subcat (C:=SGROUP) (C':=monoid) (i:=monoid_sgroup)
    (homC':=fun E F : monoid =>
            Build_subtype_image (E:=Hom (c:=SGROUP) E F)
              (subtype_image_carrier:=monoid_hom E F)
              (monoid_sgroup_hom (E:=E) (F:=F))) (CompC':=monoid_hom_comp)
    (idC':=monoid_id)).
simpl in |- *.
intros a; try assumption.
red in |- *.
auto with algebra.
simpl in |- *.
intros a b c g f; try assumption.
red in |- *.
auto with algebra.
Defined.