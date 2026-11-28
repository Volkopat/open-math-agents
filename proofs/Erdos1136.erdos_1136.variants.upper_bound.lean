import FormalConjectures.ErdosProblems.«1136»

/-! Reflect each selected point into its complement at a power of two. -/

open Set Filter Finset

theorem OMA.solution : type_of% @Erdos1136.erdos_1136.variants.upper_bound := by
  classical
  intro A hA
  rw [lowerDensity]
  apply liminf_le_of_frequently_le (frequently_atTop.mpr ?_) (isBoundedUnder_of ⟨0, fun _ => by positivity⟩)
  intro k
  let M := 2 ^ k
  refine ⟨M + 1, k.lt_two_pow_self.le.trans (Nat.le_succ _), ?_⟩
  let U := range (M + 1)
  let S := U.filter (· ∈ A)
  have hs := filter_subset (· ∈ A) U
  have hle : S.card ≤ (U \ S).card := by
    apply card_le_card_of_injOn (fun x => M - x)
    · intro x hx
      obtain ⟨hU, hmem⟩ := mem_filter.mp hx
      have hx' := mem_range.mp hU
      exact mem_sdiff.mpr ⟨mem_range.mpr (show M - x < M + 1 by omega), fun hy =>
        hA x hmem _ (mem_filter.mp hy).2 k (show x + (M - x) = M by omega)⟩
    · intro x hx y hy h
      have h₁ := mem_range.mp (hs hx)
      have h₂ := mem_range.mp (hs hy)
      change M - x = M - y at h
      omega
  rw [card_sdiff_of_subset hs, card_range] at hle
  change S.card ≤ M + 1 - S.card at hle
  have hM : 0 < M := by dsimp [M]; positivity
  have hS : (S : Set ℕ) = A ∩ Set.Iio (M + 1) := by ext; simp [S, U, and_comm]
  simp only [partialDensity, inter_univ, univ_inter, ← hS,
    ncard_coe_finset, ncard_Iio_nat]
  apply (div_le_iff₀ (by positivity)).mpr
  have htwo : (2 : ℝ) * S.card ≤ ((M + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * S.card ≤ M + 1 by omega)
  linarith
