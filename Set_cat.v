Set Implicit Arguments.
Unset Strict Implicit.
Require Export Categories.
(** Title "The category of sets." *)
Section Def.

Lemma comp_map_map_compatible :
 forall E F G : Setoid, fun2_compatible (comp_map_map (E:=E) (F:=F) (G:=G)).
intros E F G; red in |- *.
auto with algebra.
Qed.

Definition SET : category.
apply
 (Build_category (Ob:=Setoid) (Hom:=MAP)
    (Hom_comp:=fun E F G : Setoid =>
               uncurry (comp_map_map_compatible (E:=E) (F:=F) (G:=G)))
    (Hom_id:=Id)); red in |- *; simpl in |- *; unfold Map_eq in |- *;
 auto with algebra.
Defined.
End Def.