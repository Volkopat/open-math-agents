import Mathlib

/-!
# A239050: a(n) = 4 * sigma(n)

Source: https://oeis.org/A239050
Credit: @AkiRA-COM-FP

Formalizes the OEIS A239050 conjecture (offset 1): for every `n >= 1`,
`4 * sigma(n) = sigma(3 * n)` if and only if `n` is not a multiple of `3`.
-/

namespace OMA.S_oeis_a239050

/-- The OEIS sequence A239050: `a(n) = 4 * sigma(n)`. -/
def a (n : ℕ) : ℕ :=
  4 * ArithmeticFunction.sigma 1 n

/-- For every `n >= 1`, `a(n) = sigma(3 * n)` iff `3` does not divide `n`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (a n = ArithmeticFunction.sigma 1 (3 * n) ↔ ¬ (3 ∣ n)) := by
  sorry

end OMA.S_oeis_a239050
