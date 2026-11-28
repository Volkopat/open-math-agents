import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Bala's zeta(5) series conjecture

Source: https://oeis.org/A013663
Peter Bala, October 29, 2023, conjecture for zeta(5).
Credit: @houyaji
-/

namespace OMA.S_oeis_a013663

open scoped BigOperators

/-- The summand indexed by `m` with the original positive index `n = m + 1`. -/
noncomputable def balaTerm (k : ℕ) (c : ℚ) (m : ℕ) : ℂ :=
  let n : ℂ := (m : ℂ) + 1
  (n ^ 2 + 2 * (k : ℂ) * n + (c : ℂ)) /
    ((∏ j ∈ Finset.range (2 * k + 1), (n + (j : ℂ))) ^ 5)

theorem main :
    ∀ k : ℕ, 1 ≤ k →
      ∃ A B c : ℚ,
        riemannZeta (5 : ℂ) = (A : ℂ) + (B : ℂ) * (∑' m : ℕ, balaTerm k c m) := by
  sorry

end OMA.S_oeis_a013663
