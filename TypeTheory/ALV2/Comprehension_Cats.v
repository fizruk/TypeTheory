(**
  [TypeTheory.ALV2.Comprehension_Cats]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
TODO
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

Set Automatic Introduction.

(* TODO: move upstream? *)
Lemma isPullback_swap
      {C : precategory}
      {a b c d : C} {f : b --> a} {g : c --> a}
      {p1 : d --> b} {p2 : d --> c} {H : p1 · f = p2 · g}
      (pb : isPullback f g p1 p2 H)
      : isPullback _ _ _ _ (! H).
Proof.
  use make_isPullback.
  intros e h k H'.
  use (iscontrweqf _ (pb e k h (! H'))).
  use (weqtotal2 (idweq _)).
  intros ?. apply weqdirprodcomm.
Defined.

Section TypeCat_to_ComprehensionCat.

  Context (C : category).

  (* TODO: we do not need full typecat to induce the displayed functor, so we should factor out the necessary part *)
  Section TypeCat_induced_DisplayedCategory_over_C.

    Context (TC : typecat_structure C).

    Definition typecat_disp_ob_mor : disp_cat_ob_mor C.
    Proof.
        use tpair.
        - apply TC.
        - intros Γ' Γ A' A f.
        exact (∑ ff : Γ' ◂ A' --> Γ ◂ A,
                        ff ;; dpr_typecat A = dpr_typecat A' ;; f).
    Defined.

    Definition typecat_disp_id_comp : disp_cat_id_comp _ typecat_disp_ob_mor.
        split.
        + intros Γ A; cbn in *.
        use tpair.
        * apply identity.
        * etrans. apply id_left. apply pathsinv0, id_right.
        + intros ? ? ? ? ? ? ? ? ff gg; cbn in *.
        use tpair.
        * apply (pr1 ff ;; pr1 gg).
        * simpl.
            etrans. apply assoc'.
            etrans. apply maponpaths, (pr2 gg).
            etrans. apply assoc.
            etrans. apply maponpaths_2, (pr2 ff).
            apply assoc'.
    Defined.

    Definition typecat_disp_data : disp_cat_data C
        := (typecat_disp_ob_mor,, typecat_disp_id_comp).

    (* NOTE: copied with slight modifications from https://github.com/UniMath/TypeTheory/blob/ad54ca1dad822e9c71acf35c27d0a39983269462/TypeTheory/Displayed_Cats/DisplayedCatFromCwDM.v#L78-L107  *)
    Definition typecat_disp_axioms : disp_cat_axioms _ typecat_disp_data.
    Proof.
        repeat apply tpair; intros; try apply homset_property.
        - (* id_left_disp *) 
        apply subtypePath.
        { intro. apply homset_property. }
        etrans. apply id_left.
        apply pathsinv0.
        etrans. refine (pr1_transportf (C⟦_,_⟧) _ _ _ _ _ _ ).
        use transportf_const.
        - (* id_right_disp *) 
        apply subtypePath.
        { intro. apply homset_property. }
        etrans. apply id_right.
        apply pathsinv0.
        etrans. refine (pr1_transportf (C⟦_,_⟧) _ _ _ _ _ _ ).
        use transportf_const.
        - (* assoc_disp *) 
        apply subtypePath.
        { intro. apply homset_property. }
        etrans. apply assoc.
        apply pathsinv0.
        etrans. unfold mor_disp.
        refine (pr1_transportf (C⟦_,_⟧) _ _ _ _ _ _ ).
        use transportf_const.
        - (* homsets_disp *)
        apply (isofhleveltotal2 2).
        + apply homset_property.
        + intro. apply isasetaprop. apply homset_property.
    Defined.

    Definition typecat_disp : disp_cat C
        := (typecat_disp_data ,, typecat_disp_axioms).

    (* NOTE: copied with slight modifications from https://github.com/UniMath/TypeTheory/blob/ad54ca1dad822e9c71acf35c27d0a39983269462/TypeTheory/Displayed_Cats/DisplayedCatFromCwDM.v#L114-L143 *)
    Definition pullback_is_cartesian
               {Γ Γ' : C} {f : Γ' --> Γ}
               {A  : typecat_disp Γ} {A' : typecat_disp Γ'} (ff : A' -->[f] A)
      : (isPullback _ _ _ _ (pr2 ff)) -> is_cartesian ff.
    Proof.
      intros Hpb Δ g B hh.
      eapply iscontrweqf.
      2: { 
        use Hpb.
        + exact (Δ ◂ B).
        + exact (pr1 hh).
        + simpl in B. refine (dpr_typecat B ;; g).
        + etrans. apply (pr2 hh). apply assoc.
      }
      eapply weqcomp.
      2: apply weqtotal2asstol.
      apply weq_subtypes_iff.
      - intro. apply isapropdirprod; apply homset_property.
      - intro. apply (isofhleveltotal2 1). 
        + apply homset_property.
        + intros. apply homsets_disp.
      - intros gg; split; intros H.
        + exists (pr2 H).
          apply subtypePath.
          intro; apply homset_property.
          exact (pr1 H).
        + split.
          * exact (maponpaths pr1 (pr2 H)).
          * exact (pr1 H).
    Qed.

    Lemma is_fibration_typecat_disp : cleaving typecat_disp.
    Proof.
      intros Γ Γ' f A.
      unfold cartesian_lift.
      exists (reind_typecat A f).
      use tpair.
      + use tpair.
        * use q_typecat.
        * apply dpr_q_typecat.
      + apply pullback_is_cartesian.
        apply (isPullback_swap (reind_pb_typecat A f)).
    Defined.

  End TypeCat_induced_DisplayedCategory_over_C.

End TypeCat_to_ComprehensionCat.