import Mathlib

/-!
# A278405: a supercongruence for Sum_k C(n,2k)^2 * C(n-k,k)

Source: https://oeis.org/A278405

A278405 (offset 0): `a(n) = Sum_{k=0..n} binomial(n,2k)^2 * binomial(n-k,k)`:
1, 1, 2, 19, 110, 476, 2477, 15093, …  For example
`a(3) = C(3,0)^2*C(3,0) + C(3,2)^2*C(2,1) = 1 + 3^2*2 = 19`.

Conjecture (Zhi-Wei Sun, Nov 20 2016): for any prime `p > 5` and positive integer `n`, the
number `(a(p*n) - a(n))/(p*n)^3` is always a `p`-adic integer. (The entry notes that the weaker
statement with `p^3*n^2` in place of `(p*n)^3` has been proved.)

Conventions:
- `a` is indexed as in the OEIS (offset 0). In the sum, `C(n, 2k)` is `0` whenever `2k > n`, so
  the truncated subtraction `n - k` causes no change.
- A rational number is a `p`-adic integer exactly when `p` does not divide its denominator in
  lowest terms. The quotient `(a(p*n) - a(n))/(p*n)^3` is formed in `ℚ` and the statement is
  that `p` does not divide its `Rat.den`.
-/

namespace OMA.S_oeis_a278405

/-- A278405: `a(n) = Sum_{k=0..n} C(n,2k)^2 * C(n-k,k)`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose (2 * k) ^ 2 * (n - k).choose k

theorem main :
    ∀ p n : ℕ, p.Prime → 5 < p → 0 < n →
      ¬ p ∣ (((a (p * n) : ℚ) - (a n : ℚ)) / ((p : ℚ) * (n : ℚ)) ^ 3).den := by
  sorry

end OMA.S_oeis_a278405
