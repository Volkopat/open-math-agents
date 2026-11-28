import OMAStatements.S_mse_1426354
import Mathlib

namespace OMA.R_mse_1426354_R1

open OMA.S_mse_1426354

/-- Every nonabundant number beyond the cutoff satisfies the stronger bound. -/
def H1 : Prop := ∀ n : ℕ, 5040 < n → ArithmeticFunction.sigma 1 n ≤ 2 * n →
    (ArithmeticFunction.sigma 1 n : ℝ) ≤ tailTerm n

def H2 : Prop := ∀ n : ℕ, 1 ≤ n → (n ≤ 5040 ∨ 2 * n < ArithmeticFunction.sigma 1 n) →
    (ArithmeticFunction.sigma 1 n : ℝ) ≤ upperBound n

theorem main : H1 → H2 → type_of% @OMA.S_mse_1426354.main := by
  intro h1 h2 n hn
  have hpos : 0 < (harmonic n : ℝ) := by
    have h := log_add_one_le_harmonic n
    exact (Real.log_pos (by exact_mod_cast (show 1 < n+1 by omega))).trans_le h
  by_cases hs : n ≤ 5040
  · exact ⟨h2 n hn (Or.inl hs), by simp [upperBound, hs], by omega⟩
  · have hu : upperBound n = tailTerm n := by simp [upperBound, hs]
    refine ⟨?_, by rw [hu]; linarith, fun _ => by rw [hu]; linarith⟩
    by_cases ha : ArithmeticFunction.sigma 1 n ≤ 2 * n
    · exact hu.symm ▸ h1 n (by omega) ha
    · exact h2 n hn (Or.inr (by omega))

end OMA.R_mse_1426354_R1
