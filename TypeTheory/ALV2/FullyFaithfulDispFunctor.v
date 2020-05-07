(*
  [TypeTheory.ALV2.FullyFaithfulDispFunctor]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**

Fully faithful displayed functors over identity functor on C
with fixed target displayed categories are completely determined
my their action on objects.

Specifically we have an equivalence [ff_disp_functor_weq] between
[ff_disp_functor] (an alias for [ff_disp_functor_on_objects])
and [ff_disp_functor_explicit] (which is a combination of
a source displayed category over C and a fully faithful functor
over identity functor on C from said category into D').

Main definitions:

- [ff_disp_functor] (same as [ff_disp_functor_on_objects]) —
  definition of fully faithful functor without (contractible) morphisms;
- [ff_disp_functor_explicit] — combination of a source displayed category
  over C and a fully faithful displayed functor (over identity functor on C)
  into D';
- [ff_disp_functor_weq] — equivalence of the two definitions;

Accessors for [ff_disp_functor]:

- [source_disp_cat_from_ff_disp_functor] — source displayed category;
- [disp_functor_from_ff_disp_functor] — displayed functor (also acts as coercion);
- [disp_functor_from_ff_disp_functor_is_ff] — proof that extracted functor is fully faithful;

*)

Require Import UniMath.MoreFoundations.PartA.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Section Auxiliary.

  (* TODO: move upstream? *)
  Lemma weqtotaltoforall3 {X : UU}
        (P1 : X → UU)
        (P2 : ∏ x : X, P1 x → UU)
        (P3 : ∏ (x : X) (y : P1 x), P2 x y → UU)
    : (∑ (p1 : ∏ x : X, P1 x) (p2 : ∏ x : X, P2 x (p1 x)), ∏ x : X, P3 x (p1 x) (p2 x))
        ≃ (∏ x : X, ∑ (p1 : P1 x) (p2 : P2 x p1), P3 x p1 p2).
  Proof.
    eapply weqcomp.
    apply (weqtotal2asstol
             (λ p1, ∏ x : X, P2 x (p1 x))
             (λ p12, ∏ x : X, P3 x (pr1 p12 x) (pr2 p12 x))
          ).
    eapply weqcomp.
    use weqtotal2. 3: apply weqtotaltoforall.
    - exact (λ p12, ∏ x : X, P3 x (pr1 (p12 x)) (pr2 (p12 x))).
    - intros x. apply idweq.

    - eapply weqcomp.
      apply (weqtotaltoforall
               (λ x : X, ∑ y : P1 x, P2 x y)
               (λ (x : X) p12, P3 x (pr1 p12) (pr2 p12))
            ).
      apply weqonsecfibers.
      intros x.
      apply weqtotal2asstor.
  Defined.

  (* TODO: move upstream? *)
  Lemma iscontr_total2
        {X : UU} {P : X → UU}
    : iscontr X → (∏ x : X, iscontr (P x)) → iscontr (∑ (x : X), P x).
  Proof.
    intros X_contr P_contr.
    use tpair.
    - exists (pr1 X_contr). apply P_contr.
    - intros xp.
      use total2_paths_f.
      + apply X_contr.
      + apply P_contr.
  Defined.

  (* TODO: move upstream? *)
  Lemma idpath_transportb
        {X : UU} (P : X → UU)
        (x : X) (p : P x)
    : transportb P (idpath x) p = p.
  Proof.
    apply idpath.
  Defined.

  (* TODO: move upstream? *)
  Lemma homot_invweq_transportb_weq
        (Z : UU)
        (z z' : Z)
        (X Y : Z → UU)
        (e : z = z')
        (w : ∏ z : Z, X z ≃ Y z)
        (x : X z')
    : invmap (w z) (transportb Y e (w z' x)) = transportb X e x.
  Proof.
    induction e.
    etrans. apply maponpaths, idpath_transportb.
    apply homotinvweqweq.
  Defined.

End Auxiliary.

Section FullyFaithfulDispFunctor.

  (* Fully faithful displayed functor (over identity functor on C) into D'
   * is completely determined by its action on objects:
   *
   * - type family of displayed objects (for the source displayed category) over objects in C
   * - mapping of said displayed objects to displayed objects in D' over C.
   * *)
  Definition ff_disp_functor_on_objects {C : category}
             (D' : disp_cat C)
    : UU
    := ∑ (ob_disp : C → UU)
       (* Fob *), ∏ (Γ : C), ob_disp Γ → D' Γ.

  Section FullyFaithfulFunctorOnMorphisms.

    Context {C : category} {D' : disp_cat C}.
    Context (D : ff_disp_functor_on_objects D').

    Definition ff_disp_functor_on_morphisms_sop : UU
      := ∑ (mord : ∏ Γ Γ', (pr1 D Γ) → (pr1 D Γ') → (Γ --> Γ') → UU)
           (functor_mord : ∏ Γ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
                           , (mord _ _ A A' f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
         , ∏ Γ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
         , isweq (functor_mord Γ Γ' A A' f).

    Definition ff_disp_functor_on_morphisms_pos : UU
      := ∏ Γ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ'),
         ∑ (mord : UU), mord ≃ (pr2 D _ A -->[ f ] pr2 D _ A').

    Definition ff_disp_functor_on_morphisms_sop_pos_weq
      : ff_disp_functor_on_morphisms_sop ≃ ff_disp_functor_on_morphisms_pos.
    Proof.
      eapply weqcomp.
      apply (weqtotaltoforall3
               (λ Γ, ∏ Γ', (pr1 D Γ) → (pr1 D Γ') → (Γ --> Γ') → UU)
               (λ Γ mord, ∏ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
                , (mord _ A A' f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
               (λ Γ mord functor_mord, 
                ∏ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
                , isweq (functor_mord Γ' A A' f))).
      apply weqonsecfibers. intros Γ.

      eapply weqcomp.
      apply (weqtotaltoforall3
               (λ Γ', (pr1 D Γ) → (pr1 D Γ') → (Γ --> Γ') → UU)
               (λ Γ' mord, ∏ (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
                , (mord A A' f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
               (λ Γ' mord functor_mord, 
                ∏ (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
                , isweq (functor_mord A A' f))).
      apply weqonsecfibers. intros Γ'.

      eapply weqcomp.
      apply (weqtotaltoforall3
               (λ A, (pr1 D Γ') → (Γ --> Γ') → UU)
               (λ A mord, ∏ (A' : pr1 D Γ') (f : Γ --> Γ')
                , (mord A' f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
               (λ A mord functor_mord, 
                ∏ (A' : pr1 D Γ') (f : Γ --> Γ')
                , isweq (functor_mord A' f))).
      apply weqonsecfibers. intros A.

      eapply weqcomp.
      apply (weqtotaltoforall3
               (λ A', (Γ --> Γ') → UU)
               (λ A' mord, ∏ (f : Γ --> Γ')
                , (mord f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
               (λ A' mord functor_mord, 
                ∏ (f : Γ --> Γ')
                , isweq (functor_mord f))).
      apply weqonsecfibers. intros A'.

      eapply weqcomp.
      apply (weqtotaltoforall3
               (λ f, UU)
               (λ f mord, mord -> (pr2 D _ A -->[ f ] pr2 D _ A'))
               (λ f mord functor_mord, isweq functor_mord)).
      apply idweq.
    Defined.

    Definition ff_disp_functor_on_morphisms_pos_iscontr
      : iscontr ff_disp_functor_on_morphisms_pos.
    Proof.
      apply impred_iscontr. intros Γ.
      apply impred_iscontr. intros Γ'.
      apply impred_iscontr. intros A.
      apply impred_iscontr. intros A'.
      apply impred_iscontr. intros f.
      use (@iscontrweqf (∑ mord : UU, mord = pr2 D Γ A -->[f] pr2 D Γ' A')).
      - use (weqtotal2 (idweq _)). intros mord. apply univalenceweq.
      - apply iscontrcoconustot.
    Defined.

    Definition ff_disp_functor_on_morphisms_pos_isaprop
      : isaprop ff_disp_functor_on_morphisms_pos.
    Proof.
      apply isapropifcontr, ff_disp_functor_on_morphisms_pos_iscontr.
    Defined.

    Definition ff_disp_functor_on_morphisms_id_pos
               (mor_weq : ff_disp_functor_on_morphisms_pos)
      : UU
      := ∏ (Γ : C) (A : pr1 D Γ),
         ∑ (mor_id : pr1 (mor_weq Γ Γ A A (identity Γ))),
         pr1 (pr2 (mor_weq Γ Γ A A (identity Γ))) mor_id
         = transportb (mor_disp (pr2 D Γ A) (pr2 D Γ A))
                      (functor_id (functor_identity C) Γ) (id_disp (pr2 D Γ A)).

    Definition ff_disp_functor_on_morphisms_id_pos_iscontr
               (mor_weq : ff_disp_functor_on_morphisms_pos)
               (mor_isaset : ∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f)))
      : iscontr (ff_disp_functor_on_morphisms_id_pos mor_weq).
    Proof.
      apply impred_iscontr. intros Γ.
      apply impred_iscontr. intros A.
      set (mord := pr1 (mor_weq Γ Γ A A (identity Γ))).
      set (mord_weq := pr2 (mor_weq Γ Γ A A (identity Γ))).
      use (@iscontrweqf (∑ mor_id : mord, mor_id = invweq mord_weq
                                                          (transportb (mor_disp (pr2 D Γ A) (pr2 D Γ A))
                                                                      (functor_id (functor_identity C) Γ) (id_disp (pr2 D Γ A))))).
      - use (weqtotal2 (idweq _)). intros mor_id. simpl.
        use weq_iso.
        + intros p. apply (maponpaths mord_weq p @ homotweqinvweq mord_weq _).
        + intros p. apply (! homotinvweqweq mord_weq _ @ maponpaths (invmap mord_weq) p).
        + intros p. apply mor_isaset.
        + intros p. apply (@homsets_disp _ D').
      - apply iscontrcoconustot.
    Defined.

    Definition ff_disp_functor_on_morphisms_comp_pos
               (mor_weq : ff_disp_functor_on_morphisms_pos)
      : UU
      := ∏ (Γ Γ' Γ'' : C)
           (A : pr1 D Γ) (A' : pr1 D Γ') (A'' : pr1 D Γ'')
           (f : Γ --> Γ') (g : Γ' --> Γ'')
           (ff : pr1 (mor_weq Γ Γ' A A' f))
           (gg : pr1 (mor_weq Γ' Γ'' A' A'' g)),
         ∑ (mor_comp : pr1 (mor_weq Γ Γ'' A A'' (f ;; g))),
         pr2 (mor_weq Γ Γ'' A A'' (f ;; g)) mor_comp
         = transportb _ (functor_comp (functor_identity C) f g)
                      (comp_disp (pr2 (mor_weq _ _ _ _ _) ff) (pr2 (mor_weq _ _ _ _ _) gg)).

    Definition ff_disp_functor_on_morphisms_comp_pos_iscontr
               (mor_weq : ff_disp_functor_on_morphisms_pos)
               (mor_isaset : ∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f)))
      : iscontr (ff_disp_functor_on_morphisms_comp_pos mor_weq).
    Proof.
      apply impred_iscontr. intros Γ.
      apply impred_iscontr. intros Γ'.
      apply impred_iscontr. intros Γ''.
      apply impred_iscontr. intros A.
      apply impred_iscontr. intros A'.
      apply impred_iscontr. intros A''.
      apply impred_iscontr. intros f.
      apply impred_iscontr. intros g.
      apply impred_iscontr. intros ff.
      apply impred_iscontr. intros gg.
      set (mord := pr1 (mor_weq Γ Γ'' A A'' (f ;; g))).
      set (mord_weq := pr2 (mor_weq Γ Γ'' A A'' (f ;; g))).
      use (@iscontrweqf (∑ mor_comp : mord,
                                      mor_comp
                                      = invweq mord_weq (transportb _ (functor_comp (functor_identity C) f g)
                                                                    (comp_disp (pr2 (mor_weq _ _ _ _ _) ff) (pr2 (mor_weq _ _ _ _ _) gg))))).
      - use (weqtotal2 (idweq _)). intros mor_id. simpl.
        use weq_iso.
        + intros p. apply (maponpaths mord_weq p @ homotweqinvweq mord_weq _).
        + intros p. apply (! homotinvweqweq mord_weq _ @ maponpaths (invmap mord_weq) p).
        + intros p. apply mor_isaset.
        + intros p. apply (@homsets_disp _ D').
      - apply iscontrcoconustot.
    Defined.

    Definition ff_disp_functor_source_mor_isaset
               (mor_weq : ff_disp_functor_on_morphisms_pos)
      : ∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f)).
    Proof.
      intros Γ Γ' f A A'.
      set (w := pr2 (mor_weq Γ Γ' A A' f)).
      use (isofhlevelweqf 2 (invweq w)).
      apply (@homsets_disp _ D').
    Defined.

    Definition ff_disp_functor_source_mor_isaset_iscontr
               (mor_weq : ff_disp_functor_on_morphisms_pos)
      : iscontr (∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f))).
    Proof.
      apply iscontraprop1.
      - apply impred_isaprop. intros Γ.
        apply impred_isaprop. intros Γ'.
        apply impred_isaprop. intros A.
        apply impred_isaprop. intros A'.
        apply impred_isaprop. intros f.
        apply isapropisaset.
      - apply ff_disp_functor_source_mor_isaset.
    Defined.

    Definition ff_disp_functor_on_morphisms_idcomp_pos : UU
      := ∑ (mor_weq : ff_disp_functor_on_morphisms_pos)
           (mor_isaset : ∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f)))
           (mor_id : ff_disp_functor_on_morphisms_id_pos mor_weq)
         , ff_disp_functor_on_morphisms_comp_pos mor_weq.

    Definition ff_disp_functor_on_morphisms_idcomp_pos_iscontr
      : iscontr ff_disp_functor_on_morphisms_idcomp_pos.
    Proof.
      apply iscontr_total2.
      - apply ff_disp_functor_on_morphisms_pos_iscontr.
      - intros mor_weq. apply iscontr_total2.
        + apply ff_disp_functor_source_mor_isaset_iscontr.
        + intros mor_isaset.
          apply iscontr_total2.
          * apply ff_disp_functor_on_morphisms_id_pos_iscontr.
            apply mor_isaset.
          * intros ?.
            apply ff_disp_functor_on_morphisms_comp_pos_iscontr.
            apply mor_isaset.
    Defined.

    Definition ff_disp_functor_on_morphisms_idcomp_sop
      := ∑ (mor_disp : ∏ {x y : C}, pr1 D x -> pr1 D y -> (x --> y) -> UU)
           (id_disp' : ∏ {x : C} (xx : pr1 D x), mor_disp xx xx (identity x))
           (comp_disp' : ∏ {x y z : C} {f : x --> y} {g : y --> z}
                           {xx : pr1 D x} {yy : pr1 D y} {zz : pr1 D z},
                         mor_disp xx yy f -> mor_disp yy zz g -> mor_disp xx zz (f ;; g))
           (homsets_disp : ∏ {x y} {f : x --> y} {xx} {yy}, isaset (mor_disp xx yy f))
           (Fmor : ∏ x y (xx : pr1 D x) (yy : pr1 D y) (f : x --> y),
                   (mor_disp xx yy f) -> (pr2 D _ xx -->[ f ] pr2 D _ yy))
           (Fid : ∏ x (xx : pr1 D x),
                  Fmor _ _ _ _ _ (id_disp' xx) = transportb _ (functor_id (functor_identity C) x) (id_disp (pr2 D _ xx)))
           (Fcomp :  ∏ x y z (xx : pr1 D x) yy zz (f : x --> y) (g : y --> z)
                       (ff : mor_disp xx yy f) (gg : mor_disp yy zz g),
                     Fmor _ _ _ _ _ (comp_disp' ff gg)
                     = transportb _ (functor_comp (functor_identity _) f g) (comp_disp (Fmor _ _ _ _ _ ff) (Fmor _ _ _ _ _ gg)))
         , ∏ x y (xx : pr1 D x) (yy : pr1 D y) (f : x --> y),
         isweq (fun ff : mor_disp xx yy f => Fmor _ _ _ _ _ ff).

    Definition ff_disp_functor_on_morphisms_idcomp_sop_pos_weq
      : ff_disp_functor_on_morphisms_idcomp_sop ≃ ff_disp_functor_on_morphisms_idcomp_pos.
    Proof.
      use weq_iso.

      - intros sop.
        set (mor_disp := pr1 sop).
        set (id_disp' := pr1 (pr2 sop)).
        set (comp_disp' := pr1 (pr2 (pr2 sop))).
        set (homsets_disp' := pr1 (pr2 (pr2 (pr2 sop)))).
        set (Fmor := pr1 (pr2 (pr2 (pr2 (pr2 sop))))).
        set (Fid := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 sop)))))).
        set (Fcomp := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
        set (Fff := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).

        exists (λ x y xx yy f, mor_disp x y xx yy f ,, Fmor x y xx yy f,, Fff x y xx yy f).
        exists homsets_disp'.
        exists (λ x xx, (id_disp' x xx ,, Fid x xx)).
        exact (λ x y z xx yy zz f g ff gg, (comp_disp' x y z f g xx yy zz ff gg ,, Fcomp x y z xx yy zz f g ff gg)).

      - intros pos.
        set (mor_disp := λ x y xx yy f, pr1 (pr1 pos x y xx yy f)).
        set (Fmor := λ x y xx yy f, pr1 (pr2 (pr1 pos x y xx yy f))).
        set (Fff := λ x y xx yy f, pr2 (pr2 (pr1 pos x y xx yy f))).
        set (homsets_disp' := pr1 (pr2 pos)).
        set (id_disp' := λ x xx, pr1 (pr1 (pr2 (pr2 pos)) x xx)).
        set (Fid := λ x xx, pr2 (pr1 (pr2 (pr2 pos)) x xx)).
        set (comp_disp' := λ x y z f g xx yy zz ff gg, pr1 (pr2 (pr2 (pr2 pos)) x y z xx yy zz f g ff gg)).
        set (Fcomp := λ x y z xx yy zz f g ff gg, pr2 (pr2 (pr2 (pr2 pos)) x y z xx yy zz f g ff gg)).

        exists mor_disp.
        exists id_disp'.
        exists comp_disp'.
        exists homsets_disp'.
        exists Fmor.
        exists Fid.
        exists Fcomp.
        exact Fff.
      - intros ?. apply idpath.
      - intros ?. apply idpath.
    Defined.

    Definition source_disp_cat_data_of_ff_disp_functor_on_morphisms_idcomp_sop
      : ff_disp_functor_on_morphisms_idcomp_sop → disp_cat_data C.
    Proof.
      intros sop.
      set (mor_disp := pr1 sop).
      set (id_disp' := pr1 (pr2 sop)).
      set (comp_disp' := pr1 (pr2 (pr2 sop))).

      use tpair.
      - exists (pr1 D). apply mor_disp.
      - exact (id_disp' , comp_disp').
    Defined.

    Definition ff_disp_functor_mor_sop : UU
      := ∑ (mor_idcomp : ff_disp_functor_on_morphisms_idcomp_sop),
         disp_cat_axioms _ (source_disp_cat_data_of_ff_disp_functor_on_morphisms_idcomp_sop
                              mor_idcomp).
    
    Definition ff_disp_functor_mor_sop_iscontr
      : iscontr ff_disp_functor_mor_sop.
    Proof.
      apply iscontr_total2.
      - apply (iscontrweqb ff_disp_functor_on_morphisms_idcomp_sop_pos_weq).
        apply ff_disp_functor_on_morphisms_idcomp_pos_iscontr.
      - intros sop.
        apply iscontr_total2.

        + apply impred_iscontr. intros Γ.
          apply impred_iscontr. intros Γ'.
          apply impred_iscontr. intros f.
          apply impred_iscontr. intros A.
          apply impred_iscontr. intros A'.
          apply impred_iscontr. intros ff.
          apply iscontraprop1. apply (pr1 (pr2 (pr2 (pr2 sop)))).
          set (id_disp' := pr1 (pr2 sop)).
          set (comp_disp' := pr1 (pr2 (pr2 sop))).
          set (Fmor := pr1 (pr2 (pr2 (pr2 (pr2 sop))))).
          set (Fid := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 sop)))))).
          set (Fcomp := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
          set (Fff := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
          set (w := λ g, (Fmor _ _ A A' g,, Fff _ _ _ _ _)).
          etrans. apply pathsinv0. apply (homotinvweqweq (w _)).
          etrans. apply maponpaths. apply Fcomp.
          etrans. apply maponpaths, maponpaths, maponpaths_2. apply Fid.
          etrans. apply maponpaths, maponpaths. apply id_left_disp.
          etrans. apply maponpaths. apply transport_b_b. simpl.
          apply homot_invweq_transportb_weq.
          
        + intros ?.
          apply iscontr_total2.

          * apply impred_iscontr. intros Γ.
            apply impred_iscontr. intros Γ'.
            apply impred_iscontr. intros f.
            apply impred_iscontr. intros A.
            apply impred_iscontr. intros A'.
            apply impred_iscontr. intros ff.
            apply iscontraprop1. apply (pr1 (pr2 (pr2 (pr2 sop)))).
            set (id_disp' := pr1 (pr2 sop)).
            set (comp_disp' := pr1 (pr2 (pr2 sop))).
            set (Fmor := pr1 (pr2 (pr2 (pr2 (pr2 sop))))).
            set (Fid := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 sop)))))).
            set (Fcomp := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
            set (Fff := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
            set (w := λ g, (Fmor _ _ A A' g,, Fff _ _ _ _ _)).
            etrans. apply pathsinv0. apply (homotinvweqweq (w _)).
            etrans. apply maponpaths. apply Fcomp.
            etrans. apply maponpaths, maponpaths, maponpaths. apply Fid.
            etrans. apply maponpaths, maponpaths. apply id_right_disp.
            etrans. apply maponpaths. apply transport_b_b. simpl.
            apply homot_invweq_transportb_weq.

          * intros ?. apply iscontr_total2.

            -- apply impred_iscontr. intros Γ.
               apply impred_iscontr. intros Γ'.
               apply impred_iscontr. intros Γ''.
               apply impred_iscontr. intros Γ'''.
               apply impred_iscontr. intros f.
               apply impred_iscontr. intros g.
               apply impred_iscontr. intros h.
               apply impred_iscontr. intros A.
               apply impred_iscontr. intros A'.
               apply impred_iscontr. intros A''.
               apply impred_iscontr. intros A'''.
               apply impred_iscontr. intros ff.
               apply impred_iscontr. intros gg.
               apply impred_iscontr. intros hh.
               apply iscontraprop1. apply (pr1 (pr2 (pr2 (pr2 sop)))).
               set (id_disp' := pr1 (pr2 sop)).
               set (comp_disp' := pr1 (pr2 (pr2 sop))).
               set (Fmor := pr1 (pr2 (pr2 (pr2 (pr2 sop))))).
               set (Fid := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 sop)))))).
               set (Fcomp := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
               set (Fff := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
               set (w := λ g, (Fmor _ _ A A''' g,, Fff _ _ _ _ _)).
               etrans. apply pathsinv0. apply (homotinvweqweq (w (f ;; (g ;; h)))).
               etrans. apply maponpaths. apply Fcomp.
               etrans. apply maponpaths, maponpaths, maponpaths. apply Fcomp.
               etrans. apply maponpaths, maponpaths. apply assoc_disp.
               etrans. apply maponpaths. apply transport_b_b.
               (* WORK IN PROGRESS *)
               etrans. apply maponpaths, maponpaths, maponpaths_2, pathsinv0, Fcomp.
               etrans. apply maponpaths, maponpaths, pathsinv0, Fcomp.
               apply homot_invweq_transportb_weq.
            -- intros ?.
               set (homsets_disp' := pr1 (pr2 (pr2 (pr2 sop)))).
               apply iscontraprop1.
               ++ apply impred_isaprop. intros Γ.
                  apply impred_isaprop. intros Γ'.
                  apply impred_isaprop. intros f.
                  apply impred_isaprop. intros A.
                  apply impred_isaprop. intros A'.
                  apply isapropisaset.
               ++ apply homsets_disp'.
    Defined.

  End FullyFaithfulFunctorOnMorphisms.

  Section FullyFaithfulFunctorWithMorphisms.

    (* Fully faithful displayed functor (over identity functor on C) into D'
     * (equipped with contractible action on morphisms). *)
    Definition ff_disp_functor_with_morphisms
               {C : category} (D' : disp_cat C)
    : UU
      := ∑ (D : ff_disp_functor_on_objects D'), ff_disp_functor_mor_sop D.

    (* Source displayed category over C
     * extracted from a fully faithful displayed functor (over identity functor on C) *)
    Definition source_disp_cat_from_ff_disp_functor_with_morphisms
               {C : category} {D' : disp_cat C}
               (Fsop : ff_disp_functor_with_morphisms D')
      : disp_cat C.
    Proof.
      set (sop := pr1 (pr2 Fsop)).

      set (ob_disp := pr1 (pr1 Fsop)).
      set (axioms_d := pr2 (pr2 Fsop)).

      set (mor_disp := pr1 sop).
      set (id_disp' := pr1 (pr2 sop)).
      set (comp_disp' := pr1 (pr2 (pr2 sop))).

      exact (((ob_disp ,, mor_disp) ,, (id_disp' , comp_disp')) ,, axioms_d).
    Defined.

    Definition disp_functor_from_ff_disp_functor_with_morphisms
               {C : category} {D' : disp_cat C}
               (Fsop : ff_disp_functor_with_morphisms D')
      : disp_functor (functor_identity C) (source_disp_cat_from_ff_disp_functor_with_morphisms Fsop) D'.
    Proof.
      set (sop := pr1 (pr2 Fsop)).

      set (Fob := pr2 (pr1 Fsop)).
      set (Fmor := pr1 (pr2 (pr2 (pr2 (pr2 sop))))).
      set (Fid := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 sop)))))).
      set (Fcomp := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).

      exact ((Fob,,Fmor),,(Fid,Fcomp)).
    Defined.

    Coercion disp_functor_from_ff_disp_functor_with_morphisms
      : ff_disp_functor_with_morphisms >-> disp_functor.

    Definition disp_functor_from_ff_disp_functor_with_morphisms_is_ff
               {C : category} {D' : disp_cat C}
               (Fsop : ff_disp_functor_with_morphisms D')
      : disp_functor_ff (disp_functor_from_ff_disp_functor_with_morphisms Fsop).
    Proof.
      set (sop := pr1 (pr2 Fsop)).
      set (Fff := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
      exact Fff.
    Defined.

    Definition ff_disp_functor_with_morphisms_eq
               {C : category} (D' : disp_cat C)
               (X Y : ff_disp_functor_with_morphisms D')
               (e : pr1 X = pr1 Y)
      : X = Y.
    Proof.
      use total2_paths_f.
      - apply e.
      - apply isapropifcontr.
        apply ff_disp_functor_mor_sop_iscontr.
    Defined.

    Definition ff_disp_functor_explicit
               {C : category} (D' : disp_cat C)
      : UU
      := ∑ (D : disp_cat C) (F : disp_functor (functor_identity _) D D'), disp_functor_ff F.
    
    Definition ff_disp_functor_with_morphisms_weq
               {C : category} {D' : disp_cat C}
      : ff_disp_functor_with_morphisms D' ≃ ff_disp_functor_explicit D'.
    Proof.
      use weq_iso.

      - intros Fsop.
        exists (source_disp_cat_from_ff_disp_functor_with_morphisms Fsop).
        exists (disp_functor_from_ff_disp_functor_with_morphisms Fsop).
        apply disp_functor_from_ff_disp_functor_with_morphisms_is_ff.

      - intros F.
        
        set (ob_disp := pr1 (pr1 (pr1 (pr1 F)))).
        set (mor_disp := pr2 (pr1 (pr1 (pr1 F)))).
        set (id_disp' := pr1 (pr2 (pr1 (pr1 F)))).
        set (comp_disp' := pr2 (pr2 (pr1 (pr1 F)))).
        set (axioms_d := pr2 (pr1 F)).
        set (homsets_disp' := pr2 (pr2 (pr2 axioms_d))).

        set (Fob := pr1 (pr1 (pr1 (pr2 F)))).
        set (Fmor := pr2 (pr1 (pr1 (pr2 F)))).
        set (Fid := pr1 (pr2 (pr1 (pr2 F)))).
        set (Fcomp := pr2 (pr2 (pr1 (pr2 F)))).
        set (Fff := pr2 (pr2 F)).

        exists (ob_disp ,, Fob).
        exists (mor_disp ,, id_disp' ,, comp_disp' ,, homsets_disp' ,, Fmor ,, Fid ,, Fcomp ,, Fff).
        exact axioms_d.

      - intros ?. apply ff_disp_functor_with_morphisms_eq. apply idpath.
      - intros ?. apply idpath.
    Defined.

    Definition ff_disp_functor_on_objects_ff_disp_functor_with_morphisms_weq
               {C : category} {D' : disp_cat C}
      : ff_disp_functor_on_objects D' ≃ ff_disp_functor_with_morphisms D'.
    Proof.
      apply invweq, weqpr1.
      intros D.
      apply ff_disp_functor_mor_sop_iscontr.
    Defined.

  End FullyFaithfulFunctorWithMorphisms.

  (* Fully faithful displayed functor (over identity functor on C) into D'. *)
  Definition ff_disp_functor
             {C : category} (D' : disp_cat C)
    : UU
    := ff_disp_functor_on_objects D'.

  Definition ff_disp_functor_weq
             {C : category} {D' : disp_cat C}
    : ff_disp_functor D' ≃ ff_disp_functor_explicit D'.
  Proof.
    eapply weqcomp. apply ff_disp_functor_on_objects_ff_disp_functor_with_morphisms_weq.
    apply ff_disp_functor_with_morphisms_weq.
  Defined.

  Definition source_disp_cat_from_ff_disp_functor
             {C : category} {D' : disp_cat C}
             (F : ff_disp_functor D')
    : disp_cat C
    := pr1 (ff_disp_functor_weq F).

  Definition disp_functor_from_ff_disp_functor
             {C : category} {D' : disp_cat C}
             (F : ff_disp_functor D')
    : disp_functor (functor_identity C) (source_disp_cat_from_ff_disp_functor F) D'
    := pr1 (pr2 (ff_disp_functor_weq F)).

  Coercion disp_functor_from_ff_disp_functor : ff_disp_functor >-> disp_functor.

  Definition disp_functor_from_ff_disp_functor_is_ff
             {C : category} {D' : disp_cat C}
             (F : ff_disp_functor D')
    : disp_functor_ff F
    := pr2 (pr2 (ff_disp_functor_weq F)).

End FullyFaithfulDispFunctor.