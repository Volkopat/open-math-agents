import Mathlib

/-!
# A208243: Number of ways to write 2n-1 = p+q, where p is a prime, and both q and q+2 are practical numbers (A005153).

Source: https://oeis.org/A208243
Credit: @eltociear

A practical number (A005153) is a positive integer `m` such that every `k ≤ σ(m)` is a sum of
distinct divisors of `m` (`1, 2, 4, 6, 8, 12, 16, 18, ...`). `a(n)` (offset 1) counts the ways to
write `2n - 1 = p + q` with `p` prime and `q`, `q + 2` both practical. The entry conjectures
(Zhi-Wei Sun):

  a(n) > 0 for all n = 3, 4, ....

`main` states that such `p`, `q` exist for every `n ≥ 3`. "A sum of distinct divisors" is the sum
of a subset of `m.divisors`; `σ(m)` is `ArithmeticFunction.sigma 1 m`.
-/

namespace OMA.S_oeis_a208243

/-- OEIS A005153: `m > 0` and every `k ≤ σ(m)` is a sum of distinct divisors of `m`. -/
def IsPractical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k ≤ ArithmeticFunction.sigma 1 m, ∃ s ⊆ m.divisors, ∑ d ∈ s, d = k

/-- The conjecture in OEIS A208243: for every `n ≥ 3`, `2n - 1 = p + q` with `p` prime and
`q`, `q + 2` practical. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ∃ p q : ℕ, p.Prime ∧ IsPractical q ∧ IsPractical (q + 2) ∧ 2 * n - 1 = p + q := by
  sorry

end OMA.S_oeis_a208243
