import Mathlib

/-!
# A240713: Number of decompositions of 2n=p1+p2 (prime p1 <= p2), where at least one other such pair 2n=p3+p4 (prime p3 <= p4) exists such that |p1-p3|= 6 or 12.

Source: https://oeis.org/A240713
Credit: @eltociear

`a(n)` (offset 1) counts the Goldbach decompositions `2n = p1 + p2` (primes `p1 ≤ p2`) for which
another decomposition `2n = p3 + p4` (primes `p3 ≤ p4`) exists with `|p1 - p3| = 6` or `12`.
The entry conjectures:

  a(n) = 0 only when n = 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 34, 76, 229.

`main` states that for every `n ≥ 1` outside that list, `a(n) > 0`, i.e. two such decompositions
exist. Because `|p1 - p3| ≠ 0`, the second pair is automatically different from the first.
The difference is taken in `ℤ`.
-/

namespace OMA.S_oeis_a240713

/-- `p ≤ q` are primes with `p + q = m`. -/
def IsGoldbachPair (m p q : ℕ) : Prop := p.Prime ∧ q.Prime ∧ p ≤ q ∧ p + q = m

/-- The conjecture in OEIS A240713: for every `n ≥ 1` outside the listed exceptions, `2n` has two
Goldbach decompositions `p1 + p2` and `p3 + p4` with `|p1 - p3| ∈ {6, 12}`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    n ∉ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 34, 76, 229} : Finset ℕ) →
    ∃ p₁ p₂ p₃ p₄ : ℕ, IsGoldbachPair (2 * n) p₁ p₂ ∧ IsGoldbachPair (2 * n) p₃ p₄ ∧
      (|(p₁ : ℤ) - p₃| = 6 ∨ |(p₁ : ℤ) - p₃| = 12) := by
  sorry

end OMA.S_oeis_a240713
-- ci: re-run check-proof
