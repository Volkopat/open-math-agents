import Mathlib

/-!
# A060545: `a(n) = binomial(n^2, n) / n`

Source: https://oeis.org/A060545

Peter Bala's first congruence for `a(p ^ r)` is given in the source as a consequence of a result
of Meštrović. The open statement labelled Conjecture is the congruence for `a(2 * p ^ r)`
formalized here.
-/

namespace OMA.S_oeis_a060545

/-- `a(n)` is `binomial(n^2, n) / n`, using natural-number division as in the OEIS entry. -/
def a (n : ℕ) : ℕ := Nat.choose (n ^ 2) n / n

/-- Bala's conjecture: for every prime `p ≥ 5` and positive integer `r`,
`a(2 * p ^ r)` is congruent to `4 * p ^ r - 1` modulo `p ^ (3 + r)`. -/
theorem main : ∀ p r : ℕ, p.Prime → 5 ≤ p → 0 < r →
    a (2 * p ^ r) ≡ 4 * p ^ r - 1 [MOD p ^ (3 + r)] := by
  sorry

end OMA.S_oeis_a060545
