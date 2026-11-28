import Mathlib

/-!
# A108897: `k` such that `60k^2 + 30k - 30 ± 1` is a twin prime pair.

Source: https://oeis.org/A108897
Credit: @cjchaffin

Example: `k = 1` gives `60`, and `{59, 61}` are twin primes. Consecutive terms include
`(102, 103)`, `(105, 106)`, `(143, 144)`, `(1320071, 1320072)`, …

Conjecture (on the OEIS page): there are infinitely many of these consecutive pairs.

Conventions: offset 1, so `k ≥ 1` (which also keeps the natural-number subtraction
`60k^2 + 30k - 30` from underflowing).
-/

namespace OMA.S_oeis_a108897

def f (k : ℕ) : ℕ := 60 * k ^ 2 + 30 * k - 30

def IsA108897 (k : ℕ) : Prop :=
  0 < k ∧ (f k - 1).Prime ∧ (f k + 1).Prime

theorem main : {k : ℕ | IsA108897 k ∧ IsA108897 (k + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a108897
