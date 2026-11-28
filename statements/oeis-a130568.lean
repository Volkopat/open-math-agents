import Mathlib

/-!
# A130568: Generalized Beatty sequence 1+2*floor(n*phi), which contains infinitely many primes.

Source: https://oeis.org/A130568
Credit: @Olivier31200

The OEIS entry states that this entirely odd sequence contains infinitely many
primes (following Banks' theorems). Here a(n) = 1 + 2*floor(n*phi) for n >= 1,
with phi the golden ratio.
-/

namespace OMA.S_oeis_a130568

/-- The golden ratio `(1 + sqrt 5) / 2`. -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- The generalized Beatty sequence of OEIS A130568: `a(n) = 1 + 2*floor(n*phi)`. -/
noncomputable def a (n : ℕ) : ℕ := 1 + 2 * ⌊(n : ℝ) * goldenRatio⌋₊

/-- OEIS A130568: the sequence `1 + 2*floor(n*phi)`, n >= 1, contains infinitely
many primes. -/
theorem main : {p : ℕ | p.Prime ∧ ∃ n : ℕ, 0 < n ∧ a n = p}.Infinite := by
  sorry

end OMA.S_oeis_a130568

