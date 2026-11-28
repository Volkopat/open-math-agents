import Mathlib

/-!
# A254687: Number of decompositions of 2n into sums of two primes p1 < p2 such that p2-p1-1 is also a prime.

Source: https://oeis.org/A254687
Credit: @gblacher2

Formalizes the OEIS comment: "a(n)=0 for n = 1, 2, 3, 4, 6, 18, 79. It is conjectured that
there is not any other n for which a(n)=0."

Conventions: the sequence has offset 1, so `n ≥ 1`. `a n` counts the primes `p1` such that
`p2 = 2n - p1` is a prime with `p1 < p2` and `p2 - p1 - 1` is a prime; each decomposition
`2n = p1 + p2` is determined by `p1`. The statement combines both parts of the comment:
`a n = 0` exactly for the seven listed values of `n`.
-/

namespace OMA.S_oeis_a254687

/-- A254687(n): the number of decompositions `2n = p1 + p2` with primes `p1 < p2` such that
`p2 - p1 - 1` is also prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n)).filter fun p₁ =>
    p₁.Prime ∧ p₁ < 2 * n - p₁ ∧ (2 * n - p₁).Prime ∧ (2 * n - p₁ - p₁ - 1).Prime).card

/-- For `n ≥ 1`, `a(n) = 0` if and only if `n ∈ {1, 2, 3, 4, 6, 18, 79}`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n ∈ ({1, 2, 3, 4, 6, 18, 79} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a254687
