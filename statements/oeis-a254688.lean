import Mathlib

/-!
# A254688: Number of decompositions of 2n into sums of two primes p1 < p2 such that p2-p1+1 is also a prime.

Source: https://oeis.org/A254688
Credit: @eltociear

`a(n)` (offset 1) counts the ways to write `2n = p1 + p2` with primes `p1 < p2` such that
`p2 - p1 + 1` is also prime. The entry says `a(n) = 0` for `n = 1, 2, 3, 7, 19, 31, 139`, and
conjectures:

  there is not any other n for which a(n) = 0.

`main` states that for every `n ≥ 1` outside that list, `a(n) > 0`, i.e. a decomposition exists.
Since `p1 < p2`, the natural-number subtraction `p2 - p1` is exact.
-/

namespace OMA.S_oeis_a254688

/-- The conjecture in OEIS A254688: for every `n ≥ 1` other than `1, 2, 3, 7, 19, 31, 139`,
`2n = p1 + p2` for some primes `p1 < p2` with `p2 - p1 + 1` prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → n ∉ ({1, 2, 3, 7, 19, 31, 139} : Finset ℕ) →
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ < p₂ ∧ p₁ + p₂ = 2 * n ∧ (p₂ - p₁ + 1).Prime := by
  sorry

end OMA.S_oeis_a254688
-- ci: re-run check-proof
