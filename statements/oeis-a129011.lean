import Mathlib

/-!
# A129011: a(n) = floor(n^(4/3))

Source: https://oeis.org/A129011
Credit: @niclorusso

Conjecture (Churchhouse (1971), in the comments of A129011): every positive integer N is the sum of
two elements of this sequence. (Churchhouse verified it up to N = 10,000.)

Conventions:
* The sequence has offset 0: a(n) = floor(n^(4/3)) for n >= 0, so 0 = a(0) is an element. The
  power is the real power `Real.rpow` and the floor is `Nat.floor`.
* "the sum of two elements" means a(m) + a(n) for some natural numbers m, n (not necessarily
  distinct).
-/

namespace OMA.S_oeis_a129011

/-- A129011: `a n = floor(n^(4/3))`. -/
noncomputable def a (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((4 : ℝ) / 3)⌋₊

/-- Churchhouse's conjecture on A129011: every positive integer is `a m + a n` for some `m, n`. -/
theorem main : ∀ N : ℕ, 1 ≤ N → ∃ m n : ℕ, a m + a n = N := by
  sorry

end OMA.S_oeis_a129011
