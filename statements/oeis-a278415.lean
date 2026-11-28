import Mathlib

/-!
# A278415: a supercongruence for Sum_k (-1)^k * C(n,2k) * C(n-k,k)

Source: https://oeis.org/A278415

A278415 (offset 0): `a(n) = Sum_{k=0..n} binomial(n, 2k) * binomial(n-k, k) * (-1)^k`:
1, 1, 0, -5, -16, -24, 15, 197, 576, 724, …  For example
`a(3) = C(3,0)*C(3,0) - C(3,2)*C(2,1) = 1 - 6 = -5`.

Conjecture (Zhi-Wei Sun, Nov 21 2016): for any prime `p > 3` and positive integer `n`, the
number `(a(p*n) - a(n))/(p*n)^2` is always a `p`-adic integer. (The entry notes that the weaker
statement with `p^2*n` in place of `(p*n)^2` can be shown.)

Conventions:
- `a` is indexed as in the OEIS (offset 0) and takes integer values. In the sum, `C(n, 2k)` is
  `0` whenever `2k > n`, so the truncated subtraction `n - k` causes no change.
- A rational number is a `p`-adic integer exactly when `p` does not divide its denominator in
  lowest terms. The quotient `(a(p*n) - a(n))/(p*n)^2` is formed in `ℚ` and the statement is
  that `p` does not divide its `Rat.den`.
-/

namespace OMA.S_oeis_a278415

/-- A278415: `a(n) = Sum_{k=0..n} (-1)^k * C(n,2k) * C(n-k,k)`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (n.choose (2 * k) : ℤ) * ((n - k).choose k : ℤ)

theorem main :
    ∀ p n : ℕ, p.Prime → 3 < p → 0 < n →
      ¬ p ∣ (((a (p * n) : ℚ) - (a n : ℚ)) / ((p : ℚ) * (n : ℚ)) ^ 2).den := by
  sorry

end OMA.S_oeis_a278415
