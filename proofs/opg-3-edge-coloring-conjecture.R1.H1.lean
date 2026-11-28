import OMAReductions.R_opg_3_edge_coloring_conjecture_R1

-- Step opg-3-edge-coloring-conjecture.R1.H1: hypothesis H1 of reduction opg-3-edge-coloring-conjecture.R1
-- Credit: @nnkostov

/-!
# Digon Reduction for Nowhere-Zero 4-Flows in Cubic Multigraphs

If a cubic multigraph `(V, E, src, tgt)` admits a nowhere-zero 4-flow `f : E → ℤ`
and has two distinct parallel edges `e₁ ≠ e₂` sharing endpoints, pushing `f e₁`
along the 2-cycle formed by `e₁` and `e₂` produces a flow `g` that vanishes on `e₁`,
agrees with `f` away from `{e₁, e₂}`, preserves flow conservation at every vertex,
and sends `e₂` to `± f e₃` where `e₃` is the third edge incident to `src e₁`,
so `0 < |g e₂| < 4` as well.
-/

open OMA.S_opg_3_edge_coloring_conjecture

private lemma sum_eq_of_card_one {E : Type} [DecidableEq E] (f : E → ℤ)
    {A : Finset E} {a : E} (ha : a ∈ A) (hc : A.card = 1) :
    ∑ e ∈ A, f e = f a := by
  have hsub : A.erase a = ∅ := Finset.card_eq_zero.mp (by rw [Finset.card_erase_of_mem ha, hc])
  rw [← Finset.add_sum_erase A f ha, hsub, Finset.sum_empty, add_zero]

private lemma sum_eq_of_card_two_one {E : Type} [DecidableEq E] (f : E → ℤ)
    {A : Finset E} {a : E} (ha : a ∈ A) (hc : A.card = 2) :
    ∃ b : E, ∑ e ∈ A, f e = f a + f b := by
  have hc1 : (A.erase a).card = 1 := by rw [Finset.card_erase_of_mem ha, hc]
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hc1
  exact ⟨b, by rw [← Finset.add_sum_erase A f ha, hb, Finset.sum_singleton]⟩

private lemma sum_eq_of_card_two {E : Type} [DecidableEq E] (f : E → ℤ)
    {A : Finset E} {a b : E} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hc : A.card = 2) :
    ∑ e ∈ A, f e = f a + f b := by
  have hb' : b ∈ A.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hc1 : (A.erase a).card = 1 := by rw [Finset.card_erase_of_mem ha, hc]
  rw [← Finset.add_sum_erase A f ha, sum_eq_of_card_one f hb' hc1]

private lemma sum_eq_of_card_three_two {E : Type} [DecidableEq E] (f : E → ℤ)
    {A : Finset E} {a b : E} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hc : A.card = 3) :
    ∃ c : E, ∑ e ∈ A, f e = f a + (f b + f c) := by
  have hb' : b ∈ A.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hc2 : (A.erase a).card = 2 := by rw [Finset.card_erase_of_mem ha, hc]
  obtain ⟨c, hsum⟩ := sum_eq_of_card_two_one f hb' hc2
  exact ⟨c, by rw [← Finset.add_sum_erase A f ha, hsum]⟩

theorem OMA.solution : OMA.R_opg_3_edge_coloring_conjecture_R1.H1 := by
  intro V E _ _ _ src tgt hdeg ⟨e₁, e₂, he12, _hloop1, hpar⟩ ⟨f, hf, hcons⟩
  let _ : DecidableEq E := Classical.decEq E
  let u := src e₁
  let S := Finset.univ.filter (fun e : E => src e = u)
  let T := Finset.univ.filter (fun e : E => tgt e = u)
  have hdeg_u : S.card + T.card = 3 := hdeg u
  have hcons_u : ∑ e ∈ T, f e = ∑ e ∈ S, f e := hcons u
  have he1S : e₁ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ e₁, rfl⟩
  rcases hpar with ⟨hs2, ht2⟩ | ⟨hs2, ht2⟩
  · let δ : E → ℤ := fun d => (if d = e₁ then -f e₁ else 0) + (if d = e₂ then f e₁ else 0)
    let g : E → ℤ := fun d => f d + δ d
    have hsum_δ : ∀ A : Finset E,
        ∑ d ∈ A, δ d = (if e₁ ∈ A then -f e₁ else 0) + (if e₂ ∈ A then f e₁ else 0) := by
      intro A
      simp only [δ, Finset.sum_add_distrib, Finset.sum_ite_eq']
    refine ⟨e₁, g, ?_, ?_, ?_⟩
    · simp only [g, δ, ↓reduceIte, he12, add_zero]
      ring
    · intro d hd
      by_cases hd2 : d = e₂
      · rw [hd2]
        have hg2 : g e₂ = f e₂ + f e₁ := by
          simp only [g, δ, he12.symm, ↓reduceIte, zero_add]
        have he2S : e₂ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ e₂, hs2⟩
        have hS2 : 2 ≤ S.card := by
          have he2_erase : e₂ ∈ S.erase e₁ := Finset.mem_erase.mpr ⟨he12.symm, he2S⟩
          have hpos : 0 < (S.erase e₁).card := Finset.card_pos.mpr ⟨e₂, he2_erase⟩
          rw [Finset.card_erase_of_mem he1S] at hpos
          omega
        rcases (by omega : (S.card = 3 ∧ T.card = 0) ∨ (S.card = 2 ∧ T.card = 1)) with
          ⟨hS3, hT0⟩ | ⟨hS2', hT1⟩
        · have hTempty : T = ∅ := Finset.card_eq_zero.mp hT0
          have hsumT : ∑ e ∈ T, f e = 0 := by rw [hTempty, Finset.sum_empty]
          obtain ⟨e₃, hsumS⟩ := sum_eq_of_card_three_two f he1S he2S he12 hS3
          have hval : g e₂ = -f e₃ := by omega
          rw [hval, abs_neg]
          exact hf e₃
        · obtain ⟨e₃, hTsingle⟩ := Finset.card_eq_one.mp hT1
          have hsumT : ∑ e ∈ T, f e = f e₃ := by rw [hTsingle, Finset.sum_singleton]
          have hsumS : ∑ e ∈ S, f e = f e₁ + f e₂ := sum_eq_of_card_two f he1S he2S he12 hS2'
          have hval : g e₂ = f e₃ := by omega
          rw [hval]
          exact hf e₃
      · simp only [g, δ, hd, hd2, ↓reduceIte, add_zero]
        exact hf d
    · intro w
      simp only [g, Finset.sum_add_distrib, hcons w, hsum_δ, Finset.mem_filter, Finset.mem_univ,
        true_and, hs2, ht2]
      split_ifs <;> omega
  · let δ : E → ℤ := fun d => (if d = e₁ then -f e₁ else 0) + (if d = e₂ then -f e₁ else 0)
    let g : E → ℤ := fun d => f d + δ d
    have hsum_δ : ∀ A : Finset E,
        ∑ d ∈ A, δ d = (if e₁ ∈ A then -f e₁ else 0) + (if e₂ ∈ A then -f e₁ else 0) := by
      intro A
      simp only [δ, Finset.sum_add_distrib, Finset.sum_ite_eq']
    refine ⟨e₁, g, ?_, ?_, ?_⟩
    · simp only [g, δ, ↓reduceIte, he12, add_zero]
      ring
    · intro d hd
      by_cases hd2 : d = e₂
      · rw [hd2]
        have hg2 : g e₂ = f e₂ - f e₁ := by
          simp only [g, δ, he12.symm, ↓reduceIte, zero_add]
          ring
        have he2T : e₂ ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ e₂, ht2⟩
        have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨e₁, he1S⟩
        have hTpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨e₂, he2T⟩
        rcases (by omega : (S.card = 2 ∧ T.card = 1) ∨ (S.card = 1 ∧ T.card = 2)) with
          ⟨hS2, hT1⟩ | ⟨hS1, hT2⟩
        · have hsumT : ∑ e ∈ T, f e = f e₂ := sum_eq_of_card_one f he2T hT1
          obtain ⟨e₃, hsumS⟩ := sum_eq_of_card_two_one f he1S hS2
          have hval : g e₂ = f e₃ := by omega
          rw [hval]
          exact hf e₃
        · have hsumS : ∑ e ∈ S, f e = f e₁ := sum_eq_of_card_one f he1S hS1
          obtain ⟨e₃, hsumT⟩ := sum_eq_of_card_two_one f he2T hT2
          have hval : g e₂ = -f e₃ := by omega
          rw [hval, abs_neg]
          exact hf e₃
      · simp only [g, δ, hd, hd2, ↓reduceIte, add_zero]
        exact hf d
    · intro w
      simp only [g, Finset.sum_add_distrib, hcons w, hsum_δ, Finset.mem_filter, Finset.mem_univ,
        true_and, hs2, ht2]
      omega
