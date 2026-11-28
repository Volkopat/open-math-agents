import Mathlib

/-!
# A208246: Number of ways to write n = p+q with p prime or practical, and q-4, q, q+4 all practical.

Source: https://oeis.org/A208246
Credit: @eltociear

A practical number (A005153) is a positive integer `m` such that every `k ≤ σ(m)` is a sum of
distinct divisors of `m` (`1, 2, 4, 6, 8, 12, 16, 18, ...`). `a(n)` (offset 1) counts the ways to
write `n = p + q` with `p` prime or practical and `q - 4`, `q`, `q + 4` all practical. The entry
conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 8.

`main` states that such `p`, `q` exist for every `n > 8`. In `q - 4` the natural-number
subtraction is `0` for `q ≤ 4`, and `0` is not practical (practical numbers are positive), so the
truncation adds nothing. "A sum of distinct divisors" is the sum of a subset of `m.divisors`;
`σ(m)` is `ArithmeticFunction.sigma 1 m`.
-/

namespace OMA.S_oeis_a208246

/-- OEIS A005153: `m > 0` and every `k ≤ σ(m)` is a sum of distinct divisors of `m`. -/
def IsPractical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k ≤ ArithmeticFunction.sigma 1 m, ∃ s ⊆ m.divisors, ∑ d ∈ s, d = k

/-- The conjecture in OEIS A208246: for every `n > 8`, `n = p + q` with `p` prime or practical
and `q - 4`, `q`, `q + 4` all practical. -/
theorem main : ∀ n : ℕ, 8 < n →
    ∃ p q : ℕ, (p.Prime ∨ IsPractical p) ∧ IsPractical (q - 4) ∧ IsPractical q ∧
      IsPractical (q + 4) ∧ n = p + q := by
  sorry

end OMA.S_oeis_a208246
