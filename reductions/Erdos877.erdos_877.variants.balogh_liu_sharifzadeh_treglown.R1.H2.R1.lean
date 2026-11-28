import OMAReductions.R_Erdos877_erdos_877_variants_balogh_liu_sharifzadeh_treglown_R1

-- Reduction Erdos877.erdos_877.variants.balogh_liu_sharifzadeh_treglown.R1.H2.R1 of step Erdos877.erdos_877.variants.balogh_liu_sharifzadeh_treglown.R1.H2
-- Credit: @marcusbuffett

namespace OMA.R_Erdos877_erdos_877_variants_balogh_liu_sharifzadeh_treglown_R1_H2_R1

open Filter Finset
open scoped Classical

/-- The entropy bound for families supported on subsets of size at most n/64. -/
def H1 : Prop := ∀ (s : Finset ℕ) (F : Finset (Finset ℕ)),
  F ⊆ s.powerset → (∀ A ∈ F, 64 * A.card ≤ s.card) →
  (F.card : ℝ) ≤ (2 : ℝ) ^ ((s.card : ℝ) / 4)

/-- The BLST estimate restricted to maximal sum-free sets of positive density. -/
def H2 : Prop := ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
  ((((Icc 1 n).powerset.filter (Erdos877.IsMaximalSumFree n)).filter
    (fun A => ¬ 64 * A.card ≤ n)).card : ℝ) ≤ (2 : ℝ) ^ ((1 / 4 + δ) * n)

theorem main : H1 → H2 → OMA.R_Erdos877_erdos_877_variants_balogh_liu_sharifzadeh_treglown_R1.H2 := by
  classical
  intro entropy large ε hε
  obtain ⟨N, hN⟩ := exists_nat_ge (2 / ε)
  filter_upwards [large (ε/2) (by positivity), eventually_ge_atTop N] with n hlarge hn
  let S := (Icc 1 n).powerset.filter (Erdos877.IsMaximalSumFree n)
  let small := S.filter fun A => 64 * A.card ≤ n
  have hc : (Icc 1 n).card = n := by simp
  have hs : (small.card : ℝ) ≤ (2 : ℝ)^((n : ℝ)/4) := by
    rw [← hc]
    apply entropy
    · exact (filter_subset _ _).trans (filter_subset _ _)
    · intro A hA
      simpa using (mem_filter.mp hA).2
  have hl : ((S.filter fun A => ¬ 64 * A.card ≤ n).card : ℝ) ≤ _ := hlarge
  have he : 2 / ε ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have he' := (div_le_iff₀ hε).mp he
  have hpow : (2 : ℝ)^((n : ℝ)/4) ≤ 2^((1/4+ε/2)*n) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_nonneg hε.le (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hc' := card_filter_add_card_filter_not (s := S) (p := fun A => 64*A.card ≤ n)
  change (S.card : ℝ) ≤ _
  rw [← hc', Nat.cast_add]
  calc
    _ ≤ (2:ℝ)^((1/4+ε/2)*n) + 2^((1/4+ε/2)*n) := add_le_add (hs.trans hpow) hl
    _ = (2:ℝ)^((1/4+ε/2)*n + 1) := by rw [Real.rpow_add_one (by norm_num : (2:ℝ) ≠ 0)]; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

end OMA.R_Erdos877_erdos_877_variants_balogh_liu_sharifzadeh_treglown_R1_H2_R1
