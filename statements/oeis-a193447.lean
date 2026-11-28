import Mathlib

/-!
# A193447: a(n) = ((p - 2)! + p - 1) / (p * (p - 1)) where p is the n-th prime

Source: https://oeis.org/A193447
Credit: @AkiRA-COM-FP

Formalizes the OEIS A193447 conjecture: for every integer `k >= 7`,
`((k - 2)! + k - 1) / (k * (k - 1))` is an integer if and only if `k` is prime.
-/

namespace OMA.S_oeis_a193447

/-- For `k >= 7`, `k * (k - 1)` divides `(k - 2)! + k - 1` iff `k` is prime. -/
theorem main :
    ∀ k : ℕ, 7 ≤ k →
      (k * (k - 1) ∣ (k - 2).factorial + (k - 1) ↔ k.Prime) := by
  sorry

end OMA.S_oeis_a193447
