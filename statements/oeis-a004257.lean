import Mathlib

/-!
# A004257: a(n) = round(log_2(n)).

Source: https://oeis.org/A004257
Credit: @marcelopierry

Conjecture (Mikhail Kurkov, Sep 11 2019, in the formulas of A004257):
a(n) = A000523(n^2) - A000523(n).

Conventions:
* The sequence has offset 1. log_2 is the real logarithm `Real.logb 2`, and round is Mathlib's
  `round` (round x = floor(x + 1/2)); this gives the data 0, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, ...
* A000523(m) = floor(log_2(m)) for m >= 1, which is `Nat.log 2 m`.
* The identity is stated in the integers for every n >= 1.
-/

namespace OMA.S_oeis_a004257

/-- A004257(n) = round(log_2(n)). -/
noncomputable def a (n : ℕ) : ℤ := round (Real.logb 2 n)

/-- Kurkov's conjecture: round(log_2 n) = floor(log_2 n^2) - floor(log_2 n). -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = (Nat.log 2 (n ^ 2) : ℤ) - (Nat.log 2 n : ℤ) := by
  sorry

end OMA.S_oeis_a004257
