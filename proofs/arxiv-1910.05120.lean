import OMAStatements.S_arxiv_1910_05120
import Mathlib

namespace OMA.P_arxiv_1910_05120

open OMA.S_arxiv_1910_05120

private lemma mem_explicitReflectionRules_iff {n : ℕ} {E : Finset (VisibleRule n)}
    {r : VisibleRule n} :
    r ∈ explicitReflectionRules E ↔
      ∃ (F : VisibleRule n) (_ : F ∈ E) (p : Finset ℕ × Multiset (Fin n)) (hp : p ∈ F.premises),
        r = explicitReflectionRule p.2 (F.active_nonempty p hp) := by
  unfold explicitReflectionRules
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨F, hF, p, hp, rfl⟩
    exact ⟨F, hF, p, hp, rfl⟩
  · rintro ⟨F, hF, p, hp, rfl⟩
    exact ⟨F, hF, p, hp, rfl⟩

/-- Lemma 1 of arXiv:1910.05120: a context-changing definitional equation is unsolvable. -/
private lemma lemma_context_changing {n : ℕ} (E : Finset (VisibleRule n))
    (hcc : IsContextChanging E) : ¬ IsSolvableDefEq E := by
  rintro ⟨_, _, hcut⟩
  rcases hcc with ⟨F, hF, p, hp, hp_ne⟩
  let r : VisibleRule n := explicitReflectionRule p.2 (F.active_nonempty p hp)
  have hr : r ∈ explicitReflectionRules E :=
    mem_explicitReflectionRules_iff.mpr ⟨F, hF, p, hp, rfl⟩
  obtain ⟨pR, hpR, pL, hpL, hact, hctxR, _⟩ := hcut F hF r hr
  have hpL_eq : pL = ({0}, p.2) := Finset.mem_singleton.mp hpL
  rw [hpL_eq] at hact
  have hctx_eq : pR.1 = p.1 := F.active_ctx_det pR hpR p hp hact
  exact hp_ne (hctx_eq.symm.trans hctxR)

/-- Lemma 2 of arXiv:1910.05120: a definitional equation with multiple formation rules is unsolvable. -/
private lemma lemma_multi_formation {n : ℕ} (E : Finset (VisibleRule n))
    (hcard : 1 < E.card) : ¬ IsSolvableDefEq E := by
  intro hsol
  have hnotcc : ¬ IsContextChanging E := fun h => lemma_context_changing E h hsol
  rcases hsol with ⟨_, hinj, hcut⟩
  obtain ⟨F₁, hF₁, F₂, hF₂, hne⟩ := Finset.one_lt_card.mp hcard
  have hact_ne : F₁.activeSets ≠ F₂.activeSets := fun h => hne (hinj F₁ hF₁ F₂ hF₂ h)
  -- Either some active multiset of `F₁` is not in `F₂.activeSets`, or vice versa
  have hex : (∃ acts ∈ F₁.activeSets, acts ∉ F₂.activeSets) ∨
      (∃ acts ∈ F₂.activeSets, acts ∉ F₁.activeSets) := by
    by_contra h
    push Not at h
    apply hact_ne
    ext acts
    exact ⟨h.1 acts, h.2 acts⟩
  rcases hex with ⟨acts, h1, h2⟩ | ⟨acts, h1, h2⟩
  · rcases Finset.mem_image.mp h1 with ⟨p, hp, rfl⟩
    let r := explicitReflectionRule p.2 (F₁.active_nonempty p hp)
    have hr : r ∈ explicitReflectionRules E :=
      mem_explicitReflectionRules_iff.mpr ⟨F₁, hF₁, p, hp, rfl⟩
    obtain ⟨pR, hpR, pL, hpL, hact, _, _⟩ := hcut F₂ hF₂ r hr
    have hpL_eq : pL = ({0}, p.2) := Finset.mem_singleton.mp hpL
    rw [hpL_eq] at hact
    exact h2 (Finset.mem_image.mpr ⟨pR, hpR, hact⟩)
  · rcases Finset.mem_image.mp h1 with ⟨p, hp, rfl⟩
    let r := explicitReflectionRule p.2 (F₂.active_nonempty p hp)
    have hr : r ∈ explicitReflectionRules E :=
      mem_explicitReflectionRules_iff.mpr ⟨F₂, hF₂, p, hp, rfl⟩
    obtain ⟨pR, hpR, pL, hpL, hact, _, _⟩ := hcut F₁ hF₁ r hr
    have hpL_eq : pL = ({0}, p.2) := Finset.mem_singleton.mp hpL
    rw [hpL_eq] at hact
    exact h2 (Finset.mem_image.mpr ⟨pR, hpR, hact⟩)

/-- Characterization of solvable definitional equations: singleton non-context-changing rule. -/
private lemma solvable_iff_singleton_noncc {n : ℕ} (E : Finset (VisibleRule n)) :
    IsSolvableDefEq E ↔ ∃ F : VisibleRule n, ¬ F.IsContextChanging ∧ E = {F} := by
  constructor
  · intro hsol
    have hnotcc : ¬ IsContextChanging E := fun h => lemma_context_changing E h hsol
    have hle1 : E.card ≤ 1 := by
      by_contra h
      exact lemma_multi_formation E (by omega) hsol
    have hge1 : 1 ≤ E.card := Finset.one_le_card.mpr hsol.1
    have hcard1 : E.card = 1 := le_antisymm hle1 hge1
    obtain ⟨F, rfl⟩ := Finset.card_eq_one.mp hcard1
    refine ⟨F, ?_, rfl⟩
    intro hFcc
    exact hnotcc ⟨F, Finset.mem_singleton_self F, hFcc⟩
  · rintro ⟨F, hnotcc, rfl⟩
    refine ⟨Finset.singleton_nonempty F, ?_, ?_⟩
    · intro F₁ h1 F₂ h2 _
      rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2]
    · intro rR hrR rL hrL
      rw [Finset.mem_singleton.mp hrR]
      rcases mem_explicitReflectionRules_iff.mp hrL with ⟨F', hF', p, hp, rfl⟩
      have hFeq : F' = F := Finset.mem_singleton.mp hF'
      cases hFeq
      have hctx : p.1 = F.conclCtx := by
        by_contra hne
        exact hnotcc ⟨p, hp, hne⟩
      refine ⟨p, hp, ({0}, p.2), Finset.mem_singleton_self _, rfl, hctx, rfl⟩

/-- Theorem 2 of arXiv:1910.05120: a connective satisfies the principle of reflection iff it is a
Girard synthetic connective. -/
private lemma reflection_iff_synthetic {n : ℕ} (L R : Finset (VisibleRule n)) :
    SatisfiesReflectionPrinciple L R ↔ IsSyntheticConnective L R := by
  unfold SatisfiesReflectionPrinciple IsSyntheticConnective
  constructor
  · rintro (⟨hsol, hL⟩ | ⟨hsol, hR⟩)
    · obtain ⟨F, hnotcc, rfl⟩ := (solvable_iff_singleton_noncc R).mp hsol
      exact Or.inl ⟨F, hnotcc, rfl, hL⟩
    · obtain ⟨F, hnotcc, rfl⟩ := (solvable_iff_singleton_noncc L).mp hsol
      exact Or.inr ⟨F, hnotcc, rfl, hR⟩
  · rintro (⟨F, hnotcc, rfl, hL⟩ | ⟨F, hnotcc, rfl, hR⟩)
    · exact Or.inl ⟨(solvable_iff_singleton_noncc {F}).mpr ⟨F, hnotcc, rfl⟩, hL⟩
    · exact Or.inr ⟨(solvable_iff_singleton_noncc {F}).mpr ⟨F, hnotcc, rfl⟩, hR⟩

/-- Theorem 1 / Corollary 1 of arXiv:1910.05120: equivalence of the reflection principle with
cut elimination + Deducibility of Identicals. -/
private lemma reflection_iff_cut_and_doi {n : ℕ} (L R : Finset (VisibleRule n))
    (hR_irred : ∀ F₁ ∈ R, ∀ F₂ ∈ R, F₁.activeSets ⊆ F₂.activeSets → F₁ = F₂)
    (hL_unary : ∀ r ∈ L, ∃ acts : Multiset (Fin n), ∃ h : acts ≠ 0, r = explicitReflectionRule acts h) :
    (IsSolvableDefEq R ∧ L = explicitReflectionRules R) ↔
      (MainStepCutElim L R ∧ SatisfiesDoIOn R L) := by
  constructor
  · rintro ⟨hsol, rfl⟩
    refine ⟨hsol.2.2, ?_⟩
    obtain ⟨F, hnotcc, rfl⟩ := (solvable_iff_singleton_noncc R).mp hsol
    refine ⟨F, Finset.mem_singleton_self F, hnotcc, fun p hp => ?_⟩
    refine ⟨explicitReflectionRule p.2 (F.active_nonempty p hp), ?_, rfl⟩
    exact mem_explicitReflectionRules_iff.mpr ⟨F, Finset.mem_singleton_self F, p, hp, rfl⟩
  · rintro ⟨hcut, ⟨F, hF, hF_notcc, hF_doi⟩⟩
    -- Step 1: Every `p ∈ F.premises` has its explicit reflection rule in `L`
    have hsub1 : explicitReflectionRules {F} ⊆ L := by
      intro r hr
      rcases mem_explicitReflectionRules_iff.mp hr with ⟨F', hF', p, hp, rfl⟩
      have hFeq : F' = F := Finset.mem_singleton.mp hF'
      subst hFeq
      obtain ⟨rL, hrL, hrL_prem⟩ := hF_doi p hp
      obtain ⟨acts, hacts, rfl⟩ := hL_unary rL hrL
      change ({(({0} : Finset ℕ), acts)} : Finset _) = {({0}, p.2)} at hrL_prem
      have hpair : (({0} : Finset ℕ), acts) = (({0} : Finset ℕ), p.2) := by
        have hmem : (({0} : Finset ℕ), acts) ∈ ({(({0} : Finset ℕ), p.2)} : Finset _) := by
          rw [← hrL_prem]; exact Finset.mem_singleton_self _
        exact Finset.mem_singleton.mp hmem
      have hact_eq : acts = p.2 := congrArg Prod.snd hpair
      subst hact_eq
      exact hrL
    -- Step 2: Every `r ∈ L` comes from some premise of `F` (via `hcut F hF r hr`)
    have hsub2 : L ⊆ explicitReflectionRules {F} := by
      intro r hr
      obtain ⟨acts, hacts, rfl⟩ := hL_unary r hr
      obtain ⟨pR, hpR, pL, hpL, hact, _, _⟩ := hcut F hF _ hr
      have hpL_eq : pL = ({0}, acts) := Finset.mem_singleton.mp hpL
      rw [hpL_eq] at hact
      have hact' : pR.2 = acts := hact
      refine mem_explicitReflectionRules_iff.mpr ⟨F, Finset.mem_singleton_self F, pR, hpR, ?_⟩
      subst hact'
      rfl
    have hL_eq : L = explicitReflectionRules {F} := Finset.Subset.antisymm hsub2 hsub1
    -- Step 3: Show `R = {F}` using `hcut` and irredundancy `hR_irred`
    have hR_eq : R = {F} := by
      ext F'
      simp only [Finset.mem_singleton]
      constructor
      · intro hF'
        have hact_sub : F.activeSets ⊆ F'.activeSets := by
          intro acts hacts
          rcases Finset.mem_image.mp hacts with ⟨p, hp, rfl⟩
          let r := explicitReflectionRule p.2 (F.active_nonempty p hp)
          have hr : r ∈ L := by
            rw [hL_eq]
            exact mem_explicitReflectionRules_iff.mpr ⟨F, Finset.mem_singleton_self F, p, hp, rfl⟩
          obtain ⟨pR, hpR, pL, hpL, hact, _, _⟩ := hcut F' hF' r hr
          have hpL_eq : pL = ({0}, p.2) := Finset.mem_singleton.mp hpL
          rw [hpL_eq] at hact
          exact Finset.mem_image.mpr ⟨pR, hpR, hact⟩
        exact (hR_irred F hF F' hF' hact_sub).symm
      · rintro rfl
        exact hF
    rw [hR_eq]
    exact ⟨(solvable_iff_singleton_noncc {F}).mpr ⟨F, hF_notcc, rfl⟩, hL_eq⟩

/-- Construct a non-context-changing ternary visible rule from any nonempty subset `s ⊆ Fin 3`. -/
private def ternaryRule (s : Finset (Fin 3)) (hs : s.Nonempty) : VisibleRule 3 where
  premises := s.image (fun i => ({0}, ({i} : Multiset (Fin 3))))
  conclCtx := {0}
  premises_nonempty := hs.image _
  active_nonempty := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩
    exact Multiset.singleton_ne_zero i
  active_ctx_det := by
    intro p₁ hp₁ p₂ hp₂ _
    rcases Finset.mem_image.mp hp₁ with ⟨_, _, rfl⟩
    rcases Finset.mem_image.mp hp₂ with ⟨_, _, rfl⟩
    rfl

private lemma ternaryRule_not_cc (s : Finset (Fin 3)) (hs : s.Nonempty) :
    ¬ (ternaryRule s hs).IsContextChanging := by
  rintro ⟨p, hp, hne⟩
  rcases Finset.mem_image.mp hp with ⟨_, _, rfl⟩
  exact hne rfl

private lemma ternaryRule_injective {s₁ s₂ : Finset (Fin 3)}
    (hs₁ : s₁.Nonempty) (hs₂ : s₂.Nonempty)
    (heq : ternaryRule s₁ hs₁ = ternaryRule s₂ hs₂) : s₁ = s₂ := by
  ext i
  have hprem : (ternaryRule s₁ hs₁).premises = (ternaryRule s₂ hs₂).premises :=
    congrArg VisibleRule.premises heq
  constructor
  · intro hi
    have hmem : (({0} : Finset ℕ), ({i} : Multiset (Fin 3))) ∈ (ternaryRule s₂ hs₂).premises := by
      rw [← hprem]
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hmem with ⟨j, hj, hpair⟩
    have hsing : ({j} : Multiset (Fin 3)) = {i} := congrArg Prod.snd hpair
    have hji : j = i := by simpa using hsing
    rwa [← hji]
  · intro hi
    have hmem : (({0} : Finset ℕ), ({i} : Multiset (Fin 3))) ∈ (ternaryRule s₁ hs₁).premises := by
      rw [hprem]
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hmem with ⟨j, hj, hpair⟩
    have hsing : ({j} : Multiset (Fin 3)) = {i} := congrArg Prod.snd hpair
    have hji : j = i := by simpa using hsing
    rwa [← hji]

/-- Part 5: Refutation of Sambin et al.'s conjecture — at arity 3 alone there are at least 7 > 6
distinct synthetic connectives satisfying the principle of reflection. -/
private lemma more_than_six_ternary :
    ∃ S : Finset (Finset (VisibleRule 3) × Finset (VisibleRule 3)),
      6 < S.card ∧ ∀ p ∈ S, SatisfiesReflectionPrinciple p.1 p.2 := by
  let U : Finset (Finset (Fin 3)) := Finset.univ.powerset.filter Finset.Nonempty
  let f : { s // s ∈ U } → Finset (VisibleRule 3) × Finset (VisibleRule 3) :=
    fun s =>
      let F := ternaryRule s.1 (Finset.mem_filter.mp s.2).2
      (explicitReflectionRules {F}, {F})
  refine ⟨U.attach.image f, ?_, ?_⟩
  · have hinj : Function.Injective f := by
      intro s₁ s₂ h
      have hR : ({ternaryRule s₁.1 (Finset.mem_filter.mp s₁.2).2} : Finset (VisibleRule 3)) =
          {ternaryRule s₂.1 (Finset.mem_filter.mp s₂.2).2} := congrArg Prod.snd h
      have hF : ternaryRule s₁.1 (Finset.mem_filter.mp s₁.2).2 =
          ternaryRule s₂.1 (Finset.mem_filter.mp s₂.2).2 := Finset.singleton_injective hR
      exact Subtype.ext (ternaryRule_injective _ _ hF)
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
    have hUcard : U.card = 7 := by decide
    omega
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨s, _, rfl⟩
    exact Or.inl ⟨(solvable_iff_singleton_noncc _).mpr ⟨_, ternaryRule_not_cc _ _, rfl⟩, rfl⟩

end OMA.P_arxiv_1910_05120

theorem OMA.solution : type_of% @OMA.S_arxiv_1910_05120.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n E hcc
    exact OMA.P_arxiv_1910_05120.lemma_context_changing E hcc
  · intro n E hcard
    exact OMA.P_arxiv_1910_05120.lemma_multi_formation E hcard
  · intro n L R
    exact OMA.P_arxiv_1910_05120.reflection_iff_synthetic L R
  · intro n L R hR hL
    exact OMA.P_arxiv_1910_05120.reflection_iff_cut_and_doi L R hR hL
  · exact OMA.P_arxiv_1910_05120.more_than_six_ternary
