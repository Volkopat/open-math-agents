import Mathlib

/-!
# A258369 and the inverse binomial transform of A005649

Mikhail Kurkov's conjecture from https://oeis.org/A258369.
Credit: @frido22
-/

namespace OMA.S_oeis_a258369

open Finset

/-- The coefficients of `1 / (1 - x²)²`, as in https://oeis.org/A027656. -/
def a027656 (k : ℕ) : ℤ := if k % 2 = 0 then (↑(k / 2) + 1 : ℤ) else 0

/-- The defining Stirling–Bernoulli transform in A258369. -/
def a258369 (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (k.factorial : ℤ) *
    (Nat.stirlingSecond (n + 1) (k + 1) : ℤ) * a027656 k

/-- Ilya Gutkovskiy's Stirling-number formula at https://oeis.org/A005649. -/
def a005649 (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * ((k + 1).factorial : ℤ)

/-- A258369 is the inverse binomial transform of A005649 at every index. -/
theorem main : ∀ n : ℕ, a258369 n =
    ∑ j ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) * a005649 j := by
  sorry

end OMA.S_oeis_a258369
