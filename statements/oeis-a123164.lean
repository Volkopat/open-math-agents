import Mathlib

/-!
# A123164: a supercongruence for the coefficient of x^n in ((1+x)/(1-x))^n

Source: https://oeis.org/A123164

A123164 (offset 0): `a(n) = Sum_{k=0..n} C(n,k)*C(n+k-1,k)` (formula of Paul Barry, Aug 22 2007),
the coefficient of `x^n` in `((1+x)/(1-x))^n`: 1, 2, 8, 38, 192, 1002, 5336, …

Conjecture (Peter Bala, Oct 07 2021): `a(n*p^k) ≡ a(n*p^(k-1)) (mod p^(3*k))` for every prime
`p ≥ 5` and all positive integers `n` and `k`.

Conventions:
- `a` is indexed as in the OEIS (offset 0). For `n = 0` the only summand is `k = 0`, where the
  truncated subtraction `n + k - 1 = 0` gives `C(0,0)*C(0,0) = 1 = a(0)`; for `n ≥ 1` the
  subtraction is exact. The conjecture only uses `a` at positive arguments.
- The terms are natural numbers, so the congruence is stated with `Nat.ModEq`.
- `n` and `k` are positive, as in the source; `p ≥ 5` is kept as a hypothesis (the congruence
  fails for `p = 2` and `p = 3`, e.g. `a(3) - a(1) = 36` is not divisible by `27`).
-/

namespace OMA.S_oeis_a123164

/-- A123164: `a(n) = Sum_{k=0..n} C(n,k)*C(n+k-1,k)`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * (n + k - 1).choose k

theorem main :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  sorry

end OMA.S_oeis_a123164
