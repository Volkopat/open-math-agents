import FormalConjectures.ErdosProblems.«413»

/-! Check the short window near 99840 and a finite list of witnesses covering (99840, 100000). -/

open ArithmeticFunction
open scoped Omega

private def W : List ℕ :=
  [0,10,12,16,20,22,24,30,33,39,42,45,47,48,52,56,57,60,64,70,72,76,78,80,84,88,90,92,96,
   100,104,108,110,112,114,118,120,126,128,135,138,141,144,148,150,154,156]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem OMA.solution : type_of% @Erdos413.erdos_413.variants.bigOmega_largest_barrier_lt_100k := by
  have hnear : ∀ d : Fin 16, 99824 + d.1 + Ω (99824 + d.1) ≤ 99840 := by decide +kernel
  have hcov : ∀ d : Fin 159, ∃ k ∈ W,
      k < d.1 + 1 ∧ d.1 + 1 < k + 15 ∧ d.1 + 1 < k + Ω (99840 + k) := by decide +kernel
  refine ⟨⟨by decide, fun m hm => ?_⟩, fun n ⟨hsmall, hbar⟩ => ?_⟩
  · change (m : ℝ) + (Ω m : ℝ) ≤ 99840
    suffices m + Ω m ≤ 99840 by exact_mod_cast this
    by_cases h : m < 99824
    · rcases eq_or_ne m 0 with rfl | hne
      · simp
      · by_contra! hbig
        have hle : 2 ^ Ω m ≤ m := by
          rw [cardFactors_apply]
          exact (List.pow_card_le_prod _ _ fun p hp =>
            (Nat.prime_of_mem_primeFactorsList hp).two_le).trans_eq (Nat.prod_primeFactorsList hne)
        have : 2 ^ 17 ≤ 2 ^ Ω m := pow_le_pow_right₀ (by decide) (by omega)
        omega
    · simpa [show 99824 + (m - 99824) = m by omega] using hnear ⟨m - 99824, by omega⟩
  · by_contra! hbig
    obtain ⟨k, _, hkl, _, hku⟩ := hcov ⟨n - 99841, by omega⟩
    dsimp only at hkl hku
    have hreal : ((99840 + k : ℕ) : ℝ) + (Ω (99840 + k) : ℝ) ≤ n := hbar (99840 + k) (by omega)
    have hbound : 99840 + k + Ω (99840 + k) ≤ n := by exact_mod_cast hreal
    omega
