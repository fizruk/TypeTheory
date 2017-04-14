
(** * Examples 

A typical use for displayed categories is for constructing categories of structured objects, over a given (specific or general) category. We give a few examples here:

- category of topological space as total category
- arrow precategories
- objects with N-actions
- elements, over hSet

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.Topology.Topology.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.

Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Limits.
Require Import TypeTheory.Displayed_Cats.Fibrations.

Local Open Scope mor_disp_scope.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

(** * Displayed category of groups *)

Module group.

Definition grp_structure_data (X : hSet) : UU 
  := (X -> X -> X) × X × (X -> X).
Definition mult {X : hSet} (G : grp_structure_data X)
           : X -> X -> X := pr1 G.
Definition e {X : hSet} (G : grp_structure_data X)
           : X := pr1 (pr2 G).
Definition inv {X : hSet} (G : grp_structure_data X)
           : X -> X := pr2 (pr2 G).

Definition grp_structure_axioms {X : hSet}
           (G : grp_structure_data X) : UU
  := (∏ x y z : X, mult G x (mult G y z) = mult G (mult G x y) z)
       ×
     (∏ x : X, mult G x (e G) = x)
       ×
     (∏ x : X, mult G (e G) x = x)
       ×
     (∏ x : X, mult G x (inv G x) = e G)
       ×
     (∏ x : X, mult G (inv G x) x = e G).

Definition grp_assoc {X : hSet} {G : grp_structure_data X}
           (GH : grp_structure_axioms G)
  : ∏ x y z : X, mult G x (mult G y z) = mult G (mult G x y) z := pr1 GH.
Definition grp_e_r {X : hSet} {G : grp_structure_data X}
           (GH : grp_structure_axioms G)
  : ∏ x : X, mult G x (e G) = x := pr1 (pr2 GH).
Definition grp_e_l {X : hSet} {G : grp_structure_data X}
           (GH : grp_structure_axioms G)
  : ∏ x : X, mult G (e G) x = x := pr1 (pr2 (pr2 GH)).
Definition grp_inv_r {X : hSet} {G : grp_structure_data X}
           (GH : grp_structure_axioms G)
  : ∏ x : X, mult G x (inv G x) = e G := pr1 (pr2 (pr2 (pr2 GH))).
Definition grp_inv_l {X : hSet} {G : grp_structure_data X}
           (GH : grp_structure_axioms G)
  : ∏ x : X, mult G (inv G x) x = e G := pr2 (pr2 (pr2 (pr2 GH))).

Definition grp_structure (X : hSet) : UU
  := ∑ G : grp_structure_data X, grp_structure_axioms G.
Coercion grp_data {X} (G : grp_structure X) : grp_structure_data X := pr1 G.
Coercion grp_axioms {X} (G : grp_structure X) : grp_structure_axioms _ := pr2 G.

Definition is_grp_hom {X Y : hSet} (f : X -> Y) 
           (GX : grp_structure X) (GY : grp_structure Y) : UU
           := (∏ x x', f (mult GX x x') = mult GY (f x) (f x'))
                ×
              (f (e GX) = e GY).
Definition grp_hom_mult {X Y : hSet} {f : X -> Y}
           {GX : grp_structure X} {GY : grp_structure Y} 
           (is : is_grp_hom f GX GY)
           : ∏ x x', f (mult GX x x') = mult GY (f x) (f x') := pr1 is.
Definition grp_hom_e {X Y : hSet} {f : X -> Y}
           {GX : grp_structure X} {GY : grp_structure Y} 
           (is : is_grp_hom f GX GY)
           : f (e GX) = e GY := pr2 is.

Definition isaprop_is_grp_hom {X Y : hSet} (f : X -> Y) 
           (GX : grp_structure X) (GY : grp_structure Y) 
  : isaprop (is_grp_hom f GX GY).
Proof.
  repeat apply (isofhleveldirprod);
  repeat (apply impred; intro);
  apply setproperty.
Qed.

Definition disp_grp : disp_precat hset_Precategory. 
Proof.
  use disp_struct.
  - exact grp_structure.
  - intros X Y GX GY f. exact (is_grp_hom f GX GY).
  - intros.  apply isaprop_is_grp_hom. 
  - intros. simpl.
    repeat split; intros; apply idpath.
  - intros ? ? ? ? ? ? ? ? Gf Gg  ; simpl in *;
    repeat split; intros; simpl; cbn.
    + rewrite (grp_hom_mult Gf).
      apply (grp_hom_mult Gg).
    + rewrite (grp_hom_e Gf).
      apply (grp_hom_e Gg).
Defined.


End group.





(** * Displayed category of topological spaces *)


(** TODO: upstream to Topology.Topology *)
Lemma is_lim_comp {X : UU} {U V : TopologicalSet} (f : X → U) (g : U → V) (F : Filter X) (l : U) :
  is_lim f F l → continuous_at g l →
  is_lim (funcomp f g) F (g l).
Proof.
  apply filterlim_comp.
Qed.
Lemma continuous_comp {X Y Z : TopologicalSet} (f : X → Y) (g : Y → Z) :
  continuous f → continuous g →
  continuous (funcomp f g).
Proof.
  intros Hf Hg x.
  refine (is_lim_comp _ _ _ _ _ _).
  apply Hf.
  apply Hg.
Qed.
Lemma isaprop_continuous ( x y : TopologicalSet)
  (f : x → y)
  : isaprop (continuous (λ x0 : x,  f x0)).
Proof.
  do 3 (apply impred_isaprop; intro).
  apply propproperty.
Qed.
(** END TODO *)

Definition top_disp_precat_ob_mor : disp_precat_ob_mor HSET.
Proof.
  mkpair.
  - intro X. exact (isTopologicalSet (pr1hSet X)).
  - cbn. intros X Y T U f.
    apply (@continuous (pr1hSet X,,T) (pr1hSet Y,,U) f).
Defined.

Definition top_disp_precat_data : disp_precat_data HSET.
Proof.
  exists top_disp_precat_ob_mor.
  mkpair.
  - intros X XX. cbn. unfold continuous. intros. 
    unfold continuous_at. cbn. unfold is_lim. cbn.
    unfold filterlim. cbn. unfold filter_le. cbn.
    intros. assumption.
  - intros X Y Z f g XX YY ZZ Hf Hg. 
    use (@continuous_comp (pr1hSet X,,XX) (pr1hSet Y,,YY) (pr1hSet Z,,ZZ) f g);
      assumption.
Defined.

Definition top_disp_precat_axioms : disp_precat_axioms SET top_disp_precat_data.
Proof.
  repeat split; cbn; intros; try (apply proofirrelevance, isaprop_continuous).
  apply isasetaprop. apply isaprop_continuous.
Defined.
 
Definition top_disp_precat : disp_precat SET := _ ,, top_disp_precat_axioms.


(** ** The displayed arrow category 

A very fertile example: many others can be obtained from it by reindexing. *)
Section Arrow_Disp.

Context (C:Precategory).

Definition arrow_disp_ob_mor : disp_precat_ob_mor (C × C).
Proof.
  exists (fun xy : (C × C) => (pr1 xy) --> (pr2 xy)).
  simpl; intros xx' yy' g h ff'. 
    exact (pr1 ff' ;; h = g ;; pr2 ff')%mor.
Defined.

Definition arrow_id_comp : disp_precat_id_comp _ arrow_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    eapply pathscomp0. apply id_left. apply pathsinv0, id_right.
  - simpl; intros x y z f g xx yy zz ff gg.
    eapply pathscomp0. apply @pathsinv0, assoc.
    eapply pathscomp0. apply maponpaths, gg.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0. apply cancel_postcomposition, ff.
    apply pathsinv0, assoc.
Qed.

Definition arrow_data : disp_precat_data _
  := (arrow_disp_ob_mor ,, arrow_id_comp).

Lemma arrow_axioms : disp_precat_axioms (C × C) arrow_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property. 
Qed.

Definition arrow_disp : disp_precat (C × C)
  := (arrow_data ,, arrow_axioms).

End Arrow_Disp.

(** ** Objects with N-action

For any category C, “C-objects equipped with an N-action” (or more elementarily, with an endomorphism) form a displayed category over C 
Section ZAct. 

Once we have pullbacks of displayed precategories, this can be obtained as a pullback of the previous example. *)

Section NAction.

Context (C:Precategory).

Definition NAction_disp_ob_mor : disp_precat_ob_mor C.
Proof.
  exists (fun c => c --> c).
  intros x y xx yy f. exact (f ;; yy = xx ;; f)%mor.
Defined.

Definition NAction_id_comp : disp_precat_id_comp C NAction_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    eapply pathscomp0. apply id_left. apply pathsinv0, id_right.
  - simpl; intros x y z f g xx yy zz ff gg.
    eapply pathscomp0. apply @pathsinv0, assoc.
    eapply pathscomp0. apply maponpaths, gg.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0. apply cancel_postcomposition, ff.
    apply pathsinv0, assoc.
Qed.

Definition NAction_data : disp_precat_data C
  := (NAction_disp_ob_mor ,, NAction_id_comp).

Lemma NAction_axioms : disp_precat_axioms C NAction_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property. 
Qed.

Definition NAction_disp : disp_precat C
  := (NAction_data ,, NAction_axioms).

End NAction.

(** ** Elements of sets

A presheaf on a (pre)category can be viewed as a fiberwise discrete displayed (pre)category. In fact, the universal example of this is the case corresponding to the identity functor on [SET].  So, having given the displayed category for this case, one obtains it for arbitrary presheaves by reindexing. *)

(* TODO: move? ponder? *)



Section Elements_Disp.

Definition elements_ob_mor : disp_precat_ob_mor SET.
Proof.
  use tpair.
  - simpl. exact (fun X => X).
  - simpl. intros X Y x y f. exact (f x = y).
Defined.

Lemma elements_id_comp : disp_precat_id_comp SET elements_ob_mor.
Proof.
  apply tpair; simpl.
  - intros X x. apply idpath.
  - intros X Y Z f g x y z e_fx_y e_gy_z. cbn.
    eapply pathscomp0. apply maponpaths, e_fx_y. apply e_gy_z.
Qed.

Definition elements_data : disp_precat_data SET
  := (_ ,, elements_id_comp).

Lemma elements_axioms : disp_precat_axioms SET elements_data.
Proof.
  repeat split; intros; try apply setproperty.
  apply isasetaprop; apply setproperty.
Qed.

Definition elements_universal : disp_precat SET
  := (_ ,, elements_axioms).

Definition disp_precat_of_elements {C : Precategory} (P : functor C SET)
  := reindex_disp_precat P elements_universal.

(* TODO: compare to other definitions of this in the library! *)
Definition precat_of_elements {C : Precategory} (P : functor C SET)
  := total_precat (disp_precat_of_elements P).

End Elements_Disp.


Section functor_algebras.

Context {C : Precategory} (F : functor C C).

Definition disp_precat_functor_alg_ob_mor : disp_precat_ob_mor C.
Proof.
  exists (λ c : C, F c --> c).
  intros c d a a' r. exact ( (#F r)%cat · a' = a · r).
Defined.

Definition disp_precat_functor_alg_data : disp_precat_data C.
Proof.
  exists disp_precat_functor_alg_ob_mor.
  split.
  - intros x f. cbn.
    etrans. apply maponpaths_2. apply functor_id.
    etrans. apply id_left. apply pathsinv0, id_right.
  - cbn; intros ? ? ? ? ? ? ? ? H H0.
    etrans. apply maponpaths_2. apply functor_comp.
    etrans. eapply pathsinv0. apply assoc.
    etrans. apply maponpaths. apply H0.
    etrans. apply assoc. 
    etrans. apply maponpaths_2. apply H. 
    apply pathsinv0, assoc.
Defined.

Definition disp_precat_functor_alg_axioms 
  : disp_precat_axioms C disp_precat_functor_alg_data.
Proof.
  repeat split; intros; try apply homset_property.
  apply isasetaprop. apply homset_property.
Qed.

Definition disp_precat_functor_alg : disp_precat C := _ ,, disp_precat_functor_alg_axioms.

Definition total_functor_alg : precategory := total_precat disp_precat_functor_alg.


Definition iso_cleaving_functor_alg : iso_cleaving disp_precat_functor_alg.
Proof.
  intros c c' i d.
  cbn in *.
  mkpair.
  - exact (compose (compose (functor_on_iso F i) d) (iso_inv_from_iso i)).
  - cbn. unfold iso_disp. cbn.
    mkpair.
    + abstract (
          etrans; [eapply pathsinv0; apply id_right |];
          repeat rewrite <- assoc;
          do 2 apply maponpaths;
          apply pathsinv0; apply iso_after_iso_inv
        ).
    + mkpair.
      * cbn. repeat rewrite assoc.
        rewrite <- functor_comp.
        rewrite iso_after_iso_inv.
        rewrite functor_id.
        rewrite id_left. apply idpath.
      * split; apply homset_property.
Defined.


Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Local Notation "'π'" := (pr1_precat disp_precat_functor_alg).

Definition creates_limits_functor_alg
  : creates_limits disp_precat_functor_alg.
Proof.
  intros J D x L isL.
  unfold creates_limit. cbn.
  transparent assert (FC : (cone (mapdiagram π D) (F x))).
  { use mk_cone.
    - intro j. 
      eapply compose.
      apply ((#F)%cat (coneOut L j )).
      cbn. exact (pr2 (dob D j)).
    - abstract (
      intros; cbn;
      assert (XR := pr2 (dmor D e)); cbn in XR;
      etrans; [eapply pathsinv0; apply assoc |];
      etrans; [apply maponpaths, (!XR) |];
      etrans; [apply assoc |];
      apply maponpaths_2;
      rewrite <- functor_comp;
      apply maponpaths;
      apply (coneOutCommutes L)
      ).
  }
  transparent assert (LL : (LimCone (mapdiagram π D))).
  { use mk_LimCone. apply x. apply L. apply isL. }
  mkpair.
  - mkpair.
    + mkpair.
      * use (limArrow LL). apply FC.
      * abstract (
          mkpair ;
          [
            intro j; cbn;
            set (XR := limArrowCommutes LL _ FC); cbn in XR;
            apply pathsinv0; apply XR 
          | cbn; intros i j e;
            apply subtypeEquality;
            [ intro; apply homset_property |];
            cbn; apply (coneOutCommutes L)
          ]).
    + abstract (
      intro t; cbn;
      use total2_paths_f;
      [ cbn; 
        apply (limArrowUnique LL);
        induction t as [t [H1 H2]]; cbn in *;
        intro j;
        apply pathsinv0, H1 |];
      apply proofirrelevance;
      apply isofhleveltotal2;
      [ apply impred_isaprop; intro; apply homset_property |];
      intros; do 3 (apply impred_isaprop; intro);
        apply (homset_property (total_precat _ )) 
        ).
  - cbn.
    intros x' CC.
    set (πCC := mapcone π D CC). 
    use unique_exists.
    + mkpair. 
      * cbn. 
        use (limArrow LL _ πCC). 
      * set (XR := limArrowCommutes LL).
        cbn in XR.
        set (H1:= coneOutCommutes CC). simpl in H1.
        destruct x' as [c a]. cbn.
        unfold disp_precat_functor_alg in a. cbn in a.
        cbn in πCC.
        transparent assert (X : (cone (mapdiagram π D) (F c))).
        { use mk_cone.
          - intro j. 
            apply (λ f, a · f). cbn.
            apply (coneOut CC j).
          - abstract (
            intros u v e; cbn;
            rewrite <- assoc;
            apply maponpaths;
            apply (maponpaths pr1 (coneOutCommutes CC _ _ _ ))
                  ).
        } 
        {
          transitivity (limArrow LL _ X).
          - apply (limArrowUnique LL).
            intro j. rewrite <- assoc.
            rewrite (limArrowCommutes LL).
            cbn.
            rewrite assoc.
            rewrite <- functor_comp.
            etrans. apply maponpaths_2. apply maponpaths.
            apply (limArrowCommutes LL). cbn.
            set (H := pr2 (coneOut CC j)).  cbn in H. apply H.
          - apply pathsinv0.
            use (limArrowUnique LL).
            intro j.
            rewrite <- assoc.
            rewrite (limArrowCommutes LL).
            cbn.
            apply idpath.            
        }
    + simpl.
      intro j.
      apply subtypeEquality.
      { intro. apply homset_property. }
      cbn. apply (limArrowCommutes LL).
    + intros.
      apply impred_isaprop. intro t. (apply (homset_property (total_precat _ ))).
    + simpl. 
      intros.
      apply subtypeEquality.
      { intro. apply homset_property. }
      apply (limArrowUnique LL).
      intro u.
      specialize (X u).
      apply (maponpaths pr1 X).
Defined.

End functor_algebras.


Section monad_algebras.

Context {C : Precategory} (T : Monad C).

Let T' : C ⟶ C := T.
Let FAlg := total_functor_alg T'.

Definition isMonadAlg (Xa : FAlg) : UU 
  := η T (pr1 Xa) · pr2 Xa = identity _ 
                                      ×
                                      (#T')%cat (pr2 Xa) · pr2 Xa = μ T _ · pr2 Xa.

Definition disp_precat_monad_alg_ob_mor : disp_precat_ob_mor FAlg.
Proof.
  mkpair.
  - exact (λ Xa, isMonadAlg Xa).
  - cbn; intros. exact unit.
Defined.

Definition disp_precat_monad_alg_data : disp_precat_data FAlg.
Proof.
  exists disp_precat_monad_alg_ob_mor.
  split; intros; exact tt.
Defined.

Definition disp_precat_monad_alg_axioms : disp_precat_axioms _ disp_precat_monad_alg_data.
Proof.
  repeat split; cbn; intros; try apply isconnectedunit.
  apply isasetunit.
Defined.

Definition disp_precat_monad_alg_over_functor_alg : disp_precat _ 
  := _ ,, disp_precat_monad_alg_axioms.



Definition disp_precat_monad_alg : disp_precat C 
  := sigma_disp_precat disp_precat_monad_alg_over_functor_alg.

End monad_algebras.

(** * Any category is a displayed category over unit *)

Require Import UniMath.CategoryTheory.categories.StandardCategories.

Section over_terminal_category.

Variable C : Precategory.

Definition disp_over_unit_data : disp_precat_data unit_category.
Proof.
  mkpair.
  - mkpair.
    + intro. apply (ob C).
    + simpl. intros x y c c' e. apply (C ⟦c, c'⟧).
  - mkpair.
    + simpl. intros. apply identity.
    + intros ? ? ? ? ? a b c f g. 
      apply (compose (C:=C) f g ).
Defined.

Definition disp_over_unit_axioms : disp_precat_axioms _ disp_over_unit_data.
Proof.
  repeat split; cbn; intros.
  - apply id_left.
  - etrans. apply id_right.
    apply pathsinv0. unfold mor_disp. cbn.
    apply transportf_const.
  - etrans. apply assoc.
    apply pathsinv0. unfold mor_disp. cbn.
    apply transportf_const.
  - apply homset_property.
Qed.

Definition disp_over_unit : disp_precat _ := _ ,, disp_over_unit_axioms.

End over_terminal_category.

Section cartesian_product_pb.

Variable C C' : Precategory.


Definition disp_cartesian : disp_precat C 
  := reindex_disp_precat (functor_to_unit C) (disp_over_unit C').

Definition cartesian : Precategory := total_precat disp_cartesian.

End cartesian_product_pb.

Section arrow.

Variable C : Precategory.

Definition disp_arrow_data : disp_precat_data (cartesian C C).
Proof.
  mkpair.
  - mkpair.
    + intro H. 
      exact (pr1 H --> pr2 H).
    + cbn. intros xy ab f g h.
      exact (compose f (pr2 h) = compose (pr1 h) g ).
  - split; intros.
    + cbn. 
      apply pathsinv0. 
      etrans. apply id_left.
      cbn in xx.
      unfold mor_disp. cbn.
      etrans. eapply pathsinv0. apply id_right.
      apply maponpaths. apply pathsinv0.
      apply transportf_const.
    + cbn in *.
      unfold mor_disp. cbn.
      etrans. apply maponpaths. apply transportf_const.
      etrans. apply assoc.
      etrans. apply maponpaths_2. apply X.
      etrans. eapply pathsinv0, assoc.
      etrans. apply maponpaths. apply X0.
      apply assoc.
Defined.

Definition disp_arrow_axioms : disp_precat_axioms _ disp_arrow_data.
Proof.
  repeat split; intros; cbn;
    try apply homset_property.
  apply isasetaprop. 
  apply homset_property.
Qed.

Definition disp_arrow : disp_precat (cartesian C C) := _ ,, disp_arrow_axioms.

Definition arrow : Precategory := total_precat disp_arrow.

Definition disp_domain_sigma : disp_precat C := sigma_disp_precat disp_arrow.

Definition domain := total_precat disp_domain_sigma.

End arrow.

Section cartesian_product.

Variables C C' : Precategory.

Definition disp_cartesian_ob_mor : disp_precat_ob_mor C.
Proof.
  mkpair.
  - exact (fun c => C').
  - cbn. intros x y x' y' f. exact (C'⟦x', y'⟧).
Defined.

Definition disp_cartesian_data : disp_precat_data C.
Proof.
  exists disp_cartesian_ob_mor.
  mkpair; cbn. 
  - intros; apply identity.
  - intros ? ? ? ? ? ? ? ? f g. apply (f · g).
Defined.

Definition disp_cartesian_axioms : disp_precat_axioms _ disp_cartesian_data.
Proof.
  repeat split; intros; cbn.
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. unfold mor_disp. cbn. apply transportf_const.
    apply idpath.
  - etrans. apply id_right.
    apply pathsinv0.
    etrans. unfold mor_disp. cbn. apply transportf_const.
    apply idpath.
  - etrans. apply assoc.
    apply pathsinv0.
    etrans. unfold mor_disp. cbn. apply transportf_const.
    apply idpath.
  - apply homset_property.
Qed.

Definition disp_cartesian' : disp_precat C := _ ,, disp_cartesian_axioms.

End cartesian_product.





(* *)