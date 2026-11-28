import OMAStatements.S_mo_251914

open CategoryTheory CategoryTheory.Limits

-- Source problem: Brendan Fong, https://mathoverflow.net/questions/251914
-- Proof credit: @grp06
theorem OMA.solution : type_of% @OMA.S_mo_251914.main := by
  intro C cat hasPullbacks hasPushouts E M A factorization stable uniqueFillers
    containsIsomorphisms composition cobaseChange N X Y f g hf hg
  constructor
  · intro hc
    exact ⟨pushout f g, pushout.inl f g, pushout.inr f g, pushout.condition, hc⟩
  · rintro ⟨T, i, j, h, hd⟩
    let inl := pushout.inl f g
    let inr := pushout.inr f g
    let P := pullback inl inr
    let Q := pullback i j
    let c : N ⟶ P := pullback.lift f g (pushout.condition (f := f) (g := g))
    let d : N ⟶ Q := pullback.lift f g h
    have compatibility : pullback.fst inl inr ≫ i = pullback.snd inl inr ≫ j := by
      have composed := congrArg (fun k => k ≫ pushout.desc i j h)
        (pullback.condition (f := inl) (g := inr))
      simpa only [inl, inr, Category.assoc, pushout.inl_desc, pushout.inr_desc]
        using composed
    let m : P ⟶ Q := pullback.lift (pullback.fst inl inr) (pullback.snd inl inr) compatibility
    have m_fst : m ≫ pullback.fst i j = pullback.fst inl inr := by
      simp only [m, pullback.lift_fst]
    have m_snd : m ≫ pullback.snd i j = pullback.snd inl inr := by
      simp only [m, pullback.lift_snd]
    letI : Mono m := by
      constructor
      intro W u v huv
      apply pullback.hom_ext
      · simpa only [Category.assoc, m_fst] using
          congrArg (fun k => k ≫ pullback.fst i j) huv
      · simpa only [Category.assoc, m_snd] using
          congrArg (fun k => k ≫ pullback.snd i j) huv
    have factor : c ≫ m = d := by
      apply pullback.hom_ext
      · simp only [Category.assoc, m_fst, c, d, pullback.lift_fst]
      · simp only [Category.assoc, m_snd, c, d, pullback.lift_snd]
    have sq : IsPullback (𝟙 N) c d m :=
      IsPullback.of_horiz_isIso_mono ⟨by simpa only [Category.id_comp] using factor.symm⟩
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hd
