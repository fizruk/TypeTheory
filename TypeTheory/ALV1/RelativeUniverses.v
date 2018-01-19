(**
  [TypeTheory.ALV1.RelativeUniverses]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**

Contents:

- Definition of universe structure on a map, relative to a functor: [fcomprehension]
- [fcomprehension] is a proposition under saturation assumptions: [isaprop_fcomprehension]
- Definition of a relative universe: [relative_universe] (due to Vladimir Voevodsky)
- Transfer of a relative universe from one functor to another: [transfer_of_rel_univ_with_ess_surj]

*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.

Set Automatic Introduction.

Local Notation "[ C , D ]" := (functor_category C D).

(** * Relative universe structures *)

(** Given a map [ p : Ũ —> U ] in a category [D], 
    and a functor [ F : C —> D ], _a comprehension structure for [p] 
    relative to [F]_ is an operation providing all pullbacks of [p] 
    along morphisms from objects of the form [F X]. *)

Section Relative_Comprehension.

Context {C D : precategory} (J : functor C D).
Context {U tU : D} (p : D ⟦tU, U⟧).

Definition fpullback_data {X : C} (f : D ⟦J X, U⟧) : UU 
  := ∑ Xf : C, C⟦Xf, X⟧ × D⟦J Xf, tU⟧.

Definition fpb_obj  {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C := pr1 T.
Definition fp {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C⟦fpb_obj T, X⟧ := pr1 (pr2 T).
Definition fq {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : D⟦ J (fpb_obj T), tU⟧ := pr2 (pr2 T).

Definition fpullback_prop {X : C} {f : D ⟦J X, U⟧} (T : fpullback_data f) : UU
  := commutes_and_is_pullback f p (#J (fp T)) (fq T).

Definition fpullback {X : C} (f : D ⟦J X, U⟧) := 
  ∑ T : fpullback_data f, fpullback_prop T.

Coercion fpullback_data_from_fpullback {X : C} {f : D ⟦J X, U⟧} (T : fpullback f) :
   fpullback_data f := pr1 T.

Definition rel_universe_structure := ∏ X (f : D⟦J X, U⟧), fpullback f.

Definition is_universe_relative_to : UU
  := ∏ (X : C) (f : D⟦J X, _ ⟧), ∥ fpullback f ∥ .

(* TODO: add arguments declaration to make [U], [tU] explicit in this 
   def not depending on [p].  
   OR make it depend on [p] (which it conceptually should, though it formally doesn’t). *)
Definition rel_universe_structure_data := ∏ X (f : D⟦ J X, U⟧), fpullback_data f.
Definition rel_universe_structure_prop (Y : rel_universe_structure_data) :=
          ∏ X f, fpullback_prop (Y X f). 

(**  An equivalent form of [rel_universe_structure], separating its data and properties by interchanging ∑ and ∏ *)
Definition weq_rel_universe_structure_ :
   rel_universe_structure ≃ ∑ Y : rel_universe_structure_data, rel_universe_structure_prop Y.
Proof.
  eapply weqcomp. Focus 2.
    set (XR:=@weqforalltototal (ob C)).
    specialize (XR (fun X => ∏ f : D⟦ J X, U⟧, fpullback_data f)). simpl in XR.
    specialize (XR (fun X pX => ∏ A, fpullback_prop  (pX  A))).
    apply XR.
  apply weqonsecfibers.
  intro X.
  apply weqforalltototal.
Defined.

End Relative_Comprehension.

(** * Uniqueness of relative universe structures under some assumptions *)

Section Relative_Comprehension_Lemmas.

Context {C : precategory} {D : category} (J : functor C D).
Context {U tU : D} (pp : D ⟦tU, U⟧).

Lemma isaprop_fpullback_prop {X : C} {f : D ⟦J X, U⟧} (T : fpullback_data J f)
  : isaprop (fpullback_prop J pp T).
Proof.
  apply isofhleveltotal2.
  - apply homset_property.
  - intros. apply isaprop_isPullback.
Qed.

Lemma isaprop_fpullback {X : C} (f : D ⟦J X, U⟧) 
      (is_c : is_univalent C)
      (HJ : fully_faithful J) (* NOTE: the weaker assumption “ff on isos” might be enough. *)
  : isaprop (fpullback J pp f).
Proof.
  apply invproofirrelevance.
  intros x x'. apply subtypeEquality.
  - intro t. apply isaprop_fpullback_prop.
  - destruct x as [x H]. 
    destruct x' as [x' H']. cbn.    
    destruct x as [a m].
    destruct x' as [a' m']. cbn in *.
    destruct H as [H isP].
    destruct H' as [H' isP'].
    use total2_paths_f.
    + unfold fpullback_prop in *.
      set (T1 := mk_Pullback _ _ _ _ _ _ isP).
      set (T2 := mk_Pullback _ _ _ _ _ _ isP').
      set (i := iso_from_Pullback_to_Pullback T1 T2). cbn in i.
      set (i' := invmap (weq_ff_functor_on_iso HJ a a') i ).
      set (TT := isotoid _ is_c i').
      apply TT.
    + cbn.
      set (XT := transportf_dirprod _ (fun a' => C⟦a', X⟧) (fun a' => D⟦J a', tU⟧)).
      cbn in XT.
      set (XT' := XT (tpair _ a m : ∑ a : C, C ⟦ a, X ⟧ × D ⟦ J a, tU ⟧ )
                     (tpair _ a' m' : ∑ a : C, C ⟦ a, X ⟧ × D ⟦ J a, tU ⟧ )).
      cbn in *.
      match goal with | [ |- transportf _ ?e _ = _ ] => set (TT := e) end.
      rewrite XT'.
      destruct m as [p q].
      destruct m' as [p' q'].
      cbn. 
      apply pathsdirprod.
      * unfold TT.
        rewrite transportf_isotoid.
        cbn.
        unfold precomp_with.
        rewrite id_right.
        rewrite id_right.
        unfold from_Pullback_to_Pullback. cbn.
        apply (invmaponpathsweq (weq_from_fully_faithful HJ _ _ )).
        assert (T:= homotweqinvweq (weq_from_fully_faithful HJ a' a)).
        cbn in *.
        rewrite functor_comp. rewrite T. clear T.
        clear XT' XT. clear TT. 
        assert (X1:= PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ isP)).
        cbn in X1.
        apply X1.
      * unfold TT. clear TT. clear XT' XT.
        match goal with |[|- transportf ?r  _ _ = _ ] => set (P:=r) end.
        etrans. 
          apply (transportf_isotoid_functor).  
        cbn. unfold precomp_with. rewrite id_right. rewrite id_right.
        assert (XX:=homotweqinvweq (weq_from_fully_faithful HJ a' a  )).
        simpl in XX. rewrite XX. simpl. cbn.
        assert (X1:= PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ isP)).
        apply X1.
Qed.

Lemma isaprop_rel_universe_structure  (is_c : is_univalent C) 
    (HJ : fully_faithful J) : isaprop (rel_universe_structure J pp).
Proof.
  do 2 (apply impred; intro).
  apply isaprop_fpullback; assumption.
Qed.

End Relative_Comprehension_Lemmas.



(**  Relative universes *)

(** A _universe relative to a functor_ is just a map in the target category, 
    equipped with a relative comprehension structure. *)

Definition relative_universe {C D : precategory} (J : functor C D) : UU
  := ∑ X : mor_total D, rel_universe_structure J X.

Definition weak_relative_universe {C D : precategory} (J : functor C D) : UU
  := ∑ X : mor_total D, is_universe_relative_to J X.

(** ** Forgetful function from relative universes to relative weak universes *)

Definition weak_from_relative_universe {C D : precategory} (J : functor C D) 
  : relative_universe J → weak_relative_universe J.
Proof.
  use bandfmap.
  - apply idfun.
  - cbn. intros p H Γ f.
    apply hinhpr. apply H.
Defined.

Lemma weq_relative_universe_weak_relative_universe {C D : category} (J : functor C D)
      (Ccat : is_univalent C) (J_ff : fully_faithful J)
  : relative_universe J ≃ weak_relative_universe J.
Proof.
  apply weqfibtototal.
  intro p.
  apply weqonsecfibers. intro Γ.
  apply weqonsecfibers. intro f.
  apply truncation_weq.
  apply (isaprop_fpullback J _ _ Ccat J_ff).
Defined.

Goal ∏ (C D : category) (J : functor C D) 
     (Ccat : is_univalent C) (J_ff : fully_faithful J)
     (X : relative_universe J),
  weak_from_relative_universe _ X = 
  weq_relative_universe_weak_relative_universe _ Ccat J_ff X.
intros; apply idpath.
Qed.    


(* Access functions for relative universes *)
Section Relative_Universe_Accessors.

Context {C D : precategory} {J : functor C D}.

(* NOTE: it would be nice to have at least [base] as a coercion, and perhaps also [mor].  But when one declarest them as such and tries to use them, they are not found (presumably since they don’t satisfy the “uniform inheritance condition”, according to a warning given at declaration time). *)

Definition mor (U : relative_universe J) : mor_total D := pr1 U.

Definition base (U : relative_universe J) : D
  := target (mor U).

Definition total (U : relative_universe J) : D
  := source (mor U).
(* TODO: would it work more cleanly to have the total come via an object of the slice over the base? *)

Definition relative_universe_fpullback (U : relative_universe J)
  : forall (X:C) (f : J X --> base U), fpullback J (mor U) f
:= pr2 U.
Coercion relative_universe_fpullback : relative_universe >-> Funclass.

End Relative_Universe_Accessors.

Section Extension_Functoriality.
(* In case J : C —> D is fully faithful, the J-pullback operation a relative universe on J is automatically functorial, and the structure morphisms are natural with respect to that.

  For general J, these data+conditions should probably be added to the definition of a relative universe.  However, for fully faithful J, they exist uniquely. *)

(* TODO: 

- define a type [rel_universe_functoriality], given as the sigma-type of the four following lemmas;
- show (by the four following lemmas, plus a little more work) that this type is contractible for fully faithful [J].
- possibly rename the current definition of relative universe to eg [simple_relative_universe], and redefine [relative_universe] to include the functoriality. 
*)

Context {C D : precategory} {J : C ⟶ D} (HJ : fully_faithful J)
  (U : relative_universe J).
 
Definition rel_universe_fpullback_mor
    {X : C} {f : J X --> base U}
    {X' : C} {f' : J X' --> base U}
    (g : X --> X') (e : # J g ;; f' = f)
  : fpb_obj _ (U X f) --> fpb_obj _ (U X' f').
Proof.
  apply (fully_faithful_inv_hom HJ).
  use (map_into_Pb _ _ _ _ _ (pr2 (pr2 (U _ _)))).
  - apply (# J). exact (fp _ _ ;; g). 
  - apply fq.
  - refine (_ @ _). { apply maponpaths_2. apply functor_comp. }
    refine (_ @ _). { apply pathsinv0, assoc. }
    refine (_ @ _). { apply maponpaths, e. }
    exact (pr1 (pr2 (U X f))).
Defined.

(* TODO: change [fpb_obj] to [fpb_ob], and make arg implicit *)
(* TODO: add access function [fpb_isPullback]. *)

Definition rel_universe_fpullback_mor_id
    {X : C} (f : J X --> base U)
    (e := maponpaths_2 _ (functor_id _ _) _ @ id_left _)
  : rel_universe_fpullback_mor (identity X) e
  = identity (fpb_obj _ (U X f)).
Proof.
  refine (_ @ _). Focus 2. { apply fully_faithful_inv_identity. } Unfocus.
  apply (maponpaths (fully_faithful_inv_hom _ _ _)). 
  apply (map_into_Pb_unique _ (pr2 (pr2 (U _ _)))).
  - refine (_ @ _). { apply Pb_map_commutes_1. }
    refine (_ @ _). { apply maponpaths, id_right. }
    apply pathsinv0, id_left.
  - refine (_ @ _). { apply Pb_map_commutes_2. }
    apply pathsinv0, id_left.
Qed.
    
Definition rel_universe_fpullback_mor_comp
    {X : C} {f : J X --> base U}
    {X' : C} {f' : J X' --> base U}
    {X'' : C} {f'' : J X'' --> base U}
    (g : X --> X') (e : # J g ;; f' = f)
    (g' : X' --> X'') (e' : # J g' ;; f'' = f')
    (e'' := (maponpaths_2 _ (functor_comp _ _ _) _)
            @ !(assoc _ _ _) @ (maponpaths _ e') @ e)
  : rel_universe_fpullback_mor (g ;; g') e''
    = rel_universe_fpullback_mor g e
    ;; rel_universe_fpullback_mor g' e'.
Proof.
  refine (_ @ _). Focus 2. { apply fully_faithful_inv_comp. } Unfocus.
  apply (maponpaths (fully_faithful_inv_hom _ _ _)).
  apply (map_into_Pb_unique _ (pr2 (pr2 (U _ _)))).
  - refine (_ @ _). { apply Pb_map_commutes_1. }
    refine (_ @ _). Focus 2.
    { apply pathsinv0.
      refine (_ @ _). { apply pathsinv0, assoc. } 
      refine (_ @ _). { apply maponpaths, Pb_map_commutes_1. }
      refine (_ @ _). { apply maponpaths, functor_comp. }
      refine (_ @ _). { apply assoc. }
      apply maponpaths_2, Pb_map_commutes_1.
    } Unfocus.
    refine (_ @ _). { apply maponpaths, assoc. }
    apply functor_comp.
  - refine (_ @ _). { apply Pb_map_commutes_2. }
    apply pathsinv0.
    refine (_ @ _). { apply pathsinv0, assoc. } 
    refine (_ @ _). { apply maponpaths, Pb_map_commutes_2. }
    apply Pb_map_commutes_2.    
Qed.

Definition rel_universe_fp_nat
    {X : C} {f : J X --> base U}
    {X' : C} {f' : J X' --> base U}
    (g : X --> X') (e : # J g ;; f' = f)
  : rel_universe_fpullback_mor g e ;; fp _ _ = fp _ _ ;; g.
Proof.
  apply (invmaponpathsweq (weq_from_fully_faithful HJ _ _)). 
  refine (_ @ _). { apply functor_comp. }
  refine (_ @ _).
    { apply maponpaths_2, (homotweqinvweq (weq_from_fully_faithful _ _ _)). }
  apply Pb_map_commutes_1.
Qed.

Definition rel_universe_fq_nat
    {X : C} {f : J X --> base U}
    {X' : C} {f' : J X' --> base U}
    (g : X --> X') (e : # J g ;; f' = f)
  : # J (rel_universe_fpullback_mor g e) ;; fq _ _ = fq _ _.
Proof.
  refine (_ @ _).
    { apply maponpaths_2, (homotweqinvweq (weq_from_fully_faithful _ _ _)). }
  apply Pb_map_commutes_2.
Qed.

End Extension_Functoriality.


(** * Transfer of relative universes *)

Section Rel_Univ_Structure_Transfer.

(** We give two sets of conditions under which a relative universe for one functor 
    can be transferred to one for another functor. 
    In each case, we start by assuming a commutative (up to iso) square of functors, 
    in which the right-hand functor _S_ preserves pullbacks. *)

Context
   {C : precategory} {D : category}
   (J : functor C D)
   (RUJ : relative_universe J)

   {C' : precategory} {D' : category}
   (J' : functor C' D')

   (R : functor C C') (S : functor D D')

   (α : [C, D'] ⟦functor_composite J S , functor_composite R J'⟧)
   (is_iso_α : is_iso α)

   (S_pb : maps_pb_squares_to_pb_squares _ _ S).

(** On top of this, we then assume either 
   - the assumptions that [R] is split essentially surjective and [S] split full; or else 
   - that [R] is essentially surjective and [S] full, plus that [J] is fully faithful 
     and [C'] saturated.  
     These last two assumptions imply uniqueness of the new comprehension structure, 
     and hence allow getting chosen inverses out of the (non-split) 
     surjectivity assumptions. 
*)

Let αiso := isopair α is_iso_α.
Let α' := inv_from_iso αiso. 
Let α'_α := nat_trans_eq_pointwise (iso_after_iso_inv αiso).
Let α_α' := nat_trans_eq_pointwise (iso_inv_after_iso αiso).

Local Definition α_iso : forall X, is_iso (pr1 α X).
Proof.
  intros.
  apply is_functor_iso_pointwise_if_iso.
  assumption.
Qed.

Local Definition α'_iso : forall X, is_iso (pr1 α' X).
Proof.
  intros.
  apply is_functor_iso_pointwise_if_iso.
  apply is_iso_inv_from_iso.
Qed.

Local Notation tU := (source (pr1 RUJ)).
Local Notation U :=  (target (pr1 RUJ)).
Local Notation pp := (morphism_from_total (pr1 RUJ)).

(** ** Transfer along split and split-full functors *)

Definition rel_universe_structure_induced_with_ess_split
    (R_es : split_ess_surj R)
    (S_sf : split_full S)
  :  rel_universe_structure J' (# S (pr1 RUJ)).
Proof.
  cbn in α, α', α'_α.
  intros X' g.
  set (Xi := R_es X'); destruct Xi as [X i]; clear R_es.
  set (f' := (α X ;; #J' i ;; g) : D' ⟦ S (J X), S U ⟧).
  destruct (S_sf _ _ f') as [f e_Sf_f']; clear S_sf.
  set (Xf :=  (pr2 RUJ) _ f); clearbody Xf.
  destruct Xf as [H A].
  destruct H as [Xf [p q]].
  destruct A as [e isPb]. cbn in e, isPb.
  assert (Sfp := S_pb _ _ _ _ _ _ _ _ _ isPb); clear S_pb.
  set (HSfp := functor_on_square D D' S e) in *; clearbody HSfp.
  use tpair.
  { exists (R Xf); split.
    - exact (#R p ;; i).
    - refine (α' Xf ;; #S q).
  }
  cbn. unfold fpullback_prop.
  use (commutes_and_is_pullback_transfer_iso _ _ _ _ _ Sfp).
  - apply identity_iso.
  - refine (iso_comp _ (functor_on_iso J' i)).
    exists (α _); apply α_iso.
  - apply identity_iso.
  - cbn. exists (α _); apply α_iso.
  - cbn. rewrite id_right.
    apply e_Sf_f'.
  - rewrite id_left. apply id_right.
  - cbn. rewrite functor_comp.
    repeat rewrite assoc. apply maponpaths_2, (nat_trans_ax α).
  - cbn. rewrite id_right. apply pathsinv0.
    rewrite assoc. eapply @pathscomp0. apply maponpaths_2, α_α'.
    apply id_left.
Qed.

Definition transfer_of_rel_univ_with_ess_split 
    (R_es : split_ess_surj R)
    (S_sf : split_full S)
  : relative_universe J'.
Proof.
  exists (morphism_as_total (#S pp)).
  apply rel_universe_structure_induced_with_ess_split; assumption.
Defined.

(** ** Transfer along surjective functors *)

Definition fpullback_induced_with_ess_surj
           (R_es : essentially_surjective R)
           (C'_sat : is_univalent C')
           (J'_ff : fully_faithful J')
           (* TODO: only “ff on isos” might suffice; see note at [isaprop_fpullback]. *)
           (S_full : full S)
           (X' : C')
           (g : D' ⟦ J' X', S U ⟧)
: fpullback J' (# S (pr1 RUJ)) g.
Proof.
  cbn in α, α', α'_α.
  set (Xi := R_es X').
  apply (squash_to_prop Xi).
    { apply (isaprop_fpullback J'); assumption. }
  intros [X i]; clear Xi R_es.
  set (f' := (α X ;; #J' i ;; g) : D' ⟦ S (J X), S U ⟧).
  set (fe := S_full _ _ f').
  apply (squash_to_prop fe).
    { apply (isaprop_fpullback J'); assumption. }
  intros [f e_Sf_f']; clear fe S_full.
  set (Xf :=  (pr2 RUJ) _ f); clearbody Xf.
  destruct Xf as [H A].
  destruct H as [Xf [p q]].
  destruct A as [e isPb]. cbn in e, isPb.
  assert (Sfp := S_pb _ _ _ _ _ _ _ _ _ isPb); clear S_pb.
  set (HSfp := functor_on_square D D' S e) in *; clearbody HSfp.
  use tpair.
  { exists (R Xf); split.
    - exact (#R p ;; i).
    - refine (α' Xf ;; #S q).
  }
  cbn. unfold fpullback_prop.
  use (commutes_and_is_pullback_transfer_iso _ _ _ _ _ Sfp).
  - apply identity_iso.
  - refine (iso_comp _ (functor_on_iso J' i)).
    exists (α _); apply α_iso.
  - apply identity_iso.
  - cbn. exists (α _); apply α_iso.
  - cbn. rewrite id_right.
    apply e_Sf_f'.
  - rewrite id_left. apply id_right.
  - cbn. rewrite functor_comp.
    repeat rewrite assoc. apply maponpaths_2, (nat_trans_ax α).
  - cbn. rewrite id_right. apply pathsinv0.
    rewrite assoc. eapply @pathscomp0. apply maponpaths_2, α_α'.
    apply id_left.
Defined.

Definition rel_universe_structure_induced_with_ess_surj
   (R_es : essentially_surjective R)
   (C'_sat : is_univalent C')
   (J'_ff : fully_faithful J')
     (* TODO: only “ff on isos” might suffice; see note at [isaprop_fpullback]. *)
   (S_full : full S)
  :  rel_universe_structure J' (# S (pr1 RUJ)).
Proof.
  cbn in α, α', α'_α.
  intros X' g.
  apply fpullback_induced_with_ess_surj; assumption.
Defined.

Definition transfer_of_rel_univ_with_ess_surj
    (R_es : essentially_surjective R)
    (C'_sat : is_univalent C')
    (J'_ff : fully_faithful J')
     (* TODO: only “ff on isos” might suffice; see note at [isaprop_fpullback]. *)
    (S_full : full S)
  : relative_universe J'.
Proof.
  exists (morphism_as_total (#S pp)).
  apply rel_universe_structure_induced_with_ess_surj; assumption.
Defined.


End Rel_Univ_Structure_Transfer.


(** ** Transfer of weak relative universes *)

(** The next section literally copies a proof from the
    preceding section, with the exception of a truncation elimination
    in the middle of the proof.
    TODO: see if one can factor out a common lemma between the
          truncated lemma below and the untruncated lemma above.
*)
    

Section Is_universe_relative_to_Transfer.

Context
   {C : precategory} {D : category}
   (J : functor C D)

   {C' : precategory} {D' : category}
   (J' : functor C' D')

   (R : functor C C') (S : functor D D')

   (α : [C, D'] ⟦functor_composite J S , functor_composite R J'⟧)
   (is_iso_α : is_iso α)

   (S_pb : maps_pb_squares_to_pb_squares _ _ S).

Let αiso := isopair α is_iso_α.
Let α' := inv_from_iso αiso. 
Let α'_α := nat_trans_eq_pointwise (iso_after_iso_inv αiso).
Let α_α' := nat_trans_eq_pointwise (iso_inv_after_iso αiso).


Context
  (R_es : essentially_surjective R)
  (C'_sat : is_univalent C')
  (J'_ff : fully_faithful J')
  (* TODO: only “ff on isos” might suffice; see note at [isaprop_fpullback]. *)
  (S_full : full S).

Section fix_a_morphism.

Variables (U tU : D) (pp : tU --> U).

Section map_on_is_universe_relativ_to.

Hypothesis is : is_universe_relative_to J pp.


Lemma mere_fpullback_transfer {X' : C'} (g : D' ⟦ J' X', S U ⟧)
  : ∥ fpullback J' (# S pp) g ∥.
Proof.
  cbn in α, α', α'_α.
  set (Xi := R_es X').
  apply (squash_to_prop Xi).
  { apply propproperty. }
  intros [X i]; clear Xi R_es.
  set (f' := (α X ;; #J' i ;; g) : D' ⟦ S (J X), S U ⟧).
  set (fe := S_full _ _ f').
  apply (squash_to_prop fe).
  { apply propproperty. } 
  intros [f e_Sf_f']; clear fe S_full.
  set (Xf' := is _ f).
  apply (squash_to_prop Xf').
  { apply propproperty. } 
  intro Xf.
  destruct Xf as [H A].
  destruct H as [Xf [p q]].
  destruct A as [e isPb]. cbn in e, isPb.
  assert (Sfp := S_pb _ _ _ _ _ _ _ _ _ isPb); clear S_pb.
  set (HSfp := functor_on_square D D' S e) in *; clearbody HSfp.
  apply hinhpr.
  use tpair.
  { exists (R Xf); split.
    - exact (#R p ;; i).
    - refine (α' Xf ;; #S q).
  }
  cbn. unfold fpullback_prop.
  use (commutes_and_is_pullback_transfer_iso _ _ _ _ _ Sfp).
  - apply identity_iso.
  - refine (iso_comp _ (functor_on_iso J' i)).
    exists (α _). apply α_iso. apply is_iso_α.
  - apply identity_iso.
  - cbn. exists (α _). apply α_iso. apply is_iso_α.
  - cbn. rewrite id_right.
    apply e_Sf_f'.
  - rewrite id_left. apply id_right.
  - cbn. rewrite functor_comp.
    repeat rewrite assoc. apply maponpaths_2, (nat_trans_ax α).
  - cbn. rewrite id_right. apply pathsinv0.
    rewrite assoc. eapply @pathscomp0. apply maponpaths_2, α_α'.
    apply id_left.
Defined.


Lemma is_universe_transfer : is_universe_relative_to J' (#S pp).
Proof.
  intros X' g.
  apply (mere_fpullback_transfer g).
Defined.

End map_on_is_universe_relativ_to.

Definition αpwiso X : iso (S (J X)) (J' (R X))
  := functor_iso_pointwise_if_iso _ _ _ _ _ α is_iso_α X.


Definition isweq_is_universe_transfer 
           (R_full : full R) 
           (S_faithful : faithful S)
  : isweq is_universe_transfer.
Proof.
  set (S_ff := full_and_faithful_implies_fully_faithful _ _ S (S_full,,S_faithful)).
  use (gradth _ _ _ _ ).
  - intro H.
    intros X f.
    set (RX := R X). set (f' := (α' : nat_trans _ _ ) X ;; #S f).
    set (Pb_RX_f' := H RX f').
    apply (squash_to_prop Pb_RX_f'). 
    { apply propproperty. }
    intro T.
    destruct T as [X1 X2].
    destruct X1 as [X' [p' q']].
    destruct X2 as [H1 H2]. cbn in H1. cbn in H2.
    unfold RX in *. clear RX. clear Pb_RX_f'.
    
    apply (squash_to_prop (R_es X')). 
    { apply propproperty. }
    intros [Xf i].
    
    (* get a preimage of [i · 'p] *)
    apply (squash_to_prop (R_full _ _ (i · p'))).
    { apply propproperty. } 
    intros [ip' Hip'].
    apply hinhpr.
    repeat (use tpair).
    + apply Xf.
    + exact ip'.
    + set (hi := (α : nat_trans _ _ ) Xf). cbn in hi.
      set (XR := hi ;; functor_on_iso J' i ;; q'). 
      exact (invmap (weq_from_fully_faithful S_ff _ _ ) XR).
    + cbn. apply (invmaponpathsweq (weq_from_fully_faithful S_ff _ _ )).
      cbn. apply pathsinv0.
      etrans. rewrite functor_comp. apply maponpaths_2.
              apply (homotweqinvweq (weq_from_fully_faithful S_ff _ _ )).
      unfold f' in H1. unfold f' in H2. clear f'.
      etrans. eapply pathsinv0. repeat rewrite <- assoc.
              apply maponpaths. apply maponpaths. apply H1.
      rewrite functor_comp.
      repeat rewrite assoc. apply maponpaths_2.
      apply pathsinv0. rewrite <- assoc. rewrite <- assoc.
      apply (iso_inv_to_left D' _ _ _ (αpwiso Xf )).
      cbn. unfold precomp_with. rewrite id_right.
      assert (XR := nat_trans_ax α').
      apply pathsinv0. 
      etrans. Focus 2. apply XR.
      cbn.
      apply pathsinv0. 
      etrans. apply maponpaths_2. apply maponpaths. 
            apply Hip'.
      rewrite functor_comp.
      apply pathsinv0, assoc.
    + cbn. 
      match goal with |[|- isPullback _ _ _ _ (?HH)] => generalize HH end.
      intro HH.
      use (isPullback_preimage_square _ _ _ _ S_ff). 
      { apply homset_property. }
      match goal with |[|- isPullback _ _ _ _ (?HH)] => generalize HH end.
      assert (XR := homotweqinvweq (weq_from_fully_faithful S_ff (J Xf) tU )).
      simpl in XR. rewrite XR.
      clear HH XR.
      intro HH.
      use (isPullback_transfer_iso _ _ _ _ _ _ H2).
      * exact (identity_iso _ ).
      * exact (iso_inv_from_iso (αpwiso _ )).
      * exact (identity_iso _ ).
      * apply (iso_comp (functor_on_iso J' (iso_inv_from_iso i)) 
                        (iso_inv_from_iso (αpwiso _ ))).
      * cbn. rewrite id_right. 
        unfold precomp_with. rewrite id_right.
        unfold f'. apply idpath.
      * rewrite id_left. rewrite id_right. apply idpath.
      * cbn. unfold precomp_with. rewrite id_right. rewrite id_right.
        assert (XR := nat_trans_ax α').
        cbn in XR. 
        etrans. Focus 2. apply assoc.
        rewrite <- XR.
        rewrite assoc.
        apply maponpaths_2.
        rewrite <- functor_comp. 
        apply maponpaths.
        apply pathsinv0.
        etrans. apply maponpaths. 
          apply Hip'.
        rewrite assoc.
        rewrite iso_after_iso_inv.
        apply id_left.
      * cbn. rewrite id_right.
        unfold precomp_with. rewrite id_right.
        apply pathsinv0.
        do 2 rewrite assoc.
        etrans. apply maponpaths_2. apply assoc4.
        etrans. apply maponpaths_2. apply maponpaths_2. apply maponpaths.
          apply α'_α.
        rewrite id_right.
        rewrite <- functor_comp.
        rewrite iso_after_iso_inv.
        rewrite functor_id.
        apply id_left.
  - intros. apply proofirrelevance. 
    do 2 (apply impred; intro); apply propproperty.
  - intros. apply proofirrelevance. 
    do 2 (apply impred; intro); apply propproperty.
Defined.

End fix_a_morphism.

Definition weak_relative_universe_transfer : 
  weak_relative_universe J -> weak_relative_universe J'.
Proof.
  use bandfmap.
  - apply (functor_on_mor_total S).
  - intro pp. cbn.
    apply is_universe_transfer.
Defined.


Definition isweq_weak_relative_universe_transfer 
           (R_full : full R)
           (isD : is_univalent D) (isD' : is_univalent D')
           (T : functor D' D)
           (eta : iso (C:=[D, D, pr2 D]) (functor_identity D) (S ∙ T))
           (eps : iso (C:=[D', D', pr2 D']) (T ∙ S) (functor_identity D'))
           (S_faithful : faithful S) 
  : isweq weak_relative_universe_transfer.
Proof.
  apply isweqbandfmap_var.
  - use isweq_equivalence_on_mor_total.
    + apply isD.
    + apply isD'.
    + apply T.
    + apply eta.
    + apply eps.
  - intro pp.
    apply isweq_is_universe_transfer.
    + apply R_full.
    + apply S_faithful.
Defined.

Definition weq_weak_relative_universe_transfer
           (R_full : full R)
           (isD : is_univalent D) (isD' : is_univalent D')
           (T : functor D' D)
           (eta : iso (C:=[D, D, pr2 D]) (functor_identity D) (S ∙ T))
           (eps : iso (C:=[D', D', pr2 D']) (T ∙ S) (functor_identity D'))
           (S_ff : fully_faithful S)
: weak_relative_universe J ≃ weak_relative_universe J'
:= weqpair _ (isweq_weak_relative_universe_transfer R_full isD isD' T eta eps S_ff).

End Is_universe_relative_to_Transfer.


(* *)