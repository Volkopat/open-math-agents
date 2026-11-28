import Mathlib

/-!
# A386827: Sum_{k=1..n} x^(n-k)/k is irreducible modulo some prime n < p < 2n(n-1)

Source: https://oeis.org/A386827

A386827 (offset 1): `a(n)` is the least prime `n < p < 2*n*(n-1)` such that the polynomial
`Sum_{k=1..n} x^(n-k)/k` is irreducible modulo `p`, or 1 if such a prime `p` does not exist:
1, 3, 7, 13, 7, 11, 83, 11, 43, 103, …  For example `a(7) = 83` since `83 = 2*7*(7-1) - 1` is the
least prime `p > 7` such that `x^6 + x^5/2 + x^4/3 + x^3/4 + x^2/5 + x/6 + 1/7` is irreducible
modulo `p`.

Conjecture (Zhi-Wei Sun, Aug 04 2025): `a(n) > 1` for all `n > 1`. In other words, for each
`n = 2, 3, …` there is a prime `p` with `n < p < 2*n*(n-1)` such that the polynomial
`Sum_{k=1..n} x^(n-k)/k` is irreducible modulo `p`.

The conjecture is stated in the entry's own in-other-words form.

Conventions: for a prime `p > n` the denominators `1, …, n` are invertible modulo `p`, and the
reduction of the polynomial modulo `p` is the polynomial over `ZMod p` with coefficients
`(k : ZMod p)⁻¹`. Irreducibility modulo `p` is `Irreducible` in the polynomial ring over
`ZMod p`.
-/

namespace OMA.S_oeis_a386827

/-- The reduction modulo `p` of `Sum_{k=1..n} x^(n-k)/k` (for `p > n`). -/
noncomputable def P (n p : ℕ) : Polynomial (ZMod p) :=
  ∑ k ∈ Finset.Icc 1 n, Polynomial.C ((k : ZMod p)⁻¹) * Polynomial.X ^ (n - k)

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p < 2 * n * (n - 1) ∧ Irreducible (P n p) := by
  sorry

end OMA.S_oeis_a386827
