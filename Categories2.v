Set Implicit Arguments.
Unset Strict Implicit.
Require Export Categories.
Section Foncteurs.
Section Def_1.
Variable C1 C2 : category.

Record functor : Type := 
  {fctr_ob :> Ob C1 -> Ob C2;
   fctr_morph :
    forall a b : Ob C1, MAP (Hom a b) (Hom (fctr_ob a) (fctr_ob b));
   im_of_id_prf :
    forall a : Ob C1,
    Equal (fctr_morph a a (Hom_id a)) (Hom_id (fctr_ob a)):Prop;
   distrib_prf :
    forall (a b c : C1) (fa : Hom a b) (fb : Hom b c),
    Equal (fctr_morph a c (Hom_comp a b c (couple fb fa)))
      (Hom_comp (fctr_ob a) (fctr_ob b) (fctr_ob c)
         (couple (fctr_morph b c fb) (fctr_morph a b fa)))}.

Record Cfunctor : Type := 
  {Cfctr_ob :> Ob C1 -> Ob C2;
   Cfctr_morph :
    forall a b : Ob C1, MAP (Hom a b) (Hom (Cfctr_ob b) (Cfctr_ob a));
   Cim_of_id_prf :
    forall a : Ob C1,
    Equal (Cfctr_morph a a (Hom_id a)) (Hom_id (Cfctr_ob a)):Prop;
   Cdistrib_prf :
    forall (a b c : C1) (fa : Hom a b) (fb : Hom b c),
    Equal (Cfctr_morph a c (Hom_comp a b c (couple fb fa)))
      (Hom_comp (Cfctr_ob c) (Cfctr_ob b) (Cfctr_ob a)
         (couple (Cfctr_morph a b fa) (Cfctr_morph b c fb)))}.
End Def_1.
End Foncteurs.
Hint Resolve im_of_id_prf Cim_of_id_prf distrib_prf Cdistrib_prf: algebra.