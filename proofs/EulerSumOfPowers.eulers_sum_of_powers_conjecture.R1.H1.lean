import OMAReductions.R_EulerSumOfPowers_eulers_sum_of_powers_conjecture_R1

-- No sum of two positive k-th powers is a k-th power when k is a multiple of 3 or of 4.
-- This is Fermat's Last Theorem for the exponents 3 and 4, which is in Mathlib (fermatLastTheoremThree,
-- fermatLastTheoremFour) and passes to multiples (FermatLastTheoremFor.mono); the Lean proof here only
-- unpacks the two-term sum. A classical case, not progress on Euler's conjecture for three or more terms.

namespace OMA.EulerTwo

theorem two_terms (k b : ℕ) (hk : 5 < k) (hd : 3 ∣ k ∨ 4 ∣ k) (a : Fin 2 → ℕ)
    (ha : ∀ i, a i > 0) : ∑ i, (a i) ^ k ≠ b ^ k := by
  have hflt : FermatLastTheoremFor k := by
    rcases hd with h | h
    · exact FermatLastTheoremFor.mono h fermatLastTheoremThree
    · exact FermatLastTheoremFor.mono h fermatLastTheoremFour
  rw [Fin.sum_univ_two]
  intro hsum
  have hk0 : k ≠ 0 := by omega
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hk0] at hsum
    have h1 : 0 < a 0 ^ k := Nat.pow_pos (ha 0)
    omega
  exact hflt (a 0) (a 1) b (ha 0).ne' (ha 1).ne' hb hsum

end OMA.EulerTwo

theorem OMA.solution : OMA.R_EulerSumOfPowers_eulers_sum_of_powers_conjecture_R1.H1 := by
  intro k b hk hd a ha
  exact OMA.EulerTwo.two_terms k b hk hd a ha
