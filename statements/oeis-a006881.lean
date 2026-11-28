import Mathlib

/-!
# A006881: Squarefree semiprimes

Source: https://oeis.org/A006881
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Squarefree semiprimes are the products of two distinct primes. Conjecture (Richard R. Forberg,
OEIS, 2015): the set of sums of two elements of the sequence includes all primes `≥ 29` and all
integers `≥ 83`.

## Encoding

* `n` is a squarefree semiprime if `n = p · q` with `p ≠ q` primes.
* "Sums of two elements" allows the two elements to be equal.
-/

namespace OMA.S_oeis_a006881

/-- `n` is a product of two distinct primes. -/
def IsSqfreeSemiprime (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q

/-- `n` is a sum of two squarefree semiprimes. -/
def IsSumOfTwo (n : ℕ) : Prop := ∃ x y : ℕ, IsSqfreeSemiprime x ∧ IsSqfreeSemiprime y ∧ n = x + y

theorem main :
    (∀ p : ℕ, p.Prime → 29 ≤ p → IsSumOfTwo p) ∧ (∀ n : ℕ, 83 ≤ n → IsSumOfTwo n) := by
  sorry

end OMA.S_oeis_a006881
