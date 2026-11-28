import Mathlib

/-!
# A093348: A 5-fractal castle starting with 0.

Source: https://oeis.org/A093348 (conjecture by Charlie Neder, May 25 2019)

The sequence (offset 1) is defined in the entry by `a(1) = 0`, then
`a(n) = w(n) - a(n - w(n))` where `w(n) = 5^floor(log(n-1)/log(5))`, i.e. `w(n)` is the
largest power of 5 not exceeding `n - 1`; in Lean `floor(log(n-1)/log(5))` is `Nat.log 5 (n-1)`.
The terms are computed in `ℤ`.

Conjecture: a(n+1) = (n mod 2) + Sum_{k=0..infinity} (4*5^k*(floor(n/5^(k+1)) mod 2)),
for every `n >= 0` (so that `n + 1` runs over the offset range). The infinite sum is finite:
for `k >= n` one has `5^(k+1) > n`, so `floor(n/5^(k+1)) = 0` and the term vanishes; the sum is
therefore taken over `k < n + 1`.
-/

namespace OMA.S_oeis_a093348

/-- A093348: `a(1) = 0`, `a(n) = w(n) - a(n - w(n))` with `w(n) = 5^floor(log_5(n-1))`. -/
def a (n : ℕ) : ℤ :=
  if h : n ≤ 1 then 0 else 5 ^ Nat.log 5 (n - 1) - a (n - 5 ^ Nat.log 5 (n - 1))
decreasing_by
  have := Nat.one_le_pow (Nat.log 5 (n - 1)) 5 (by norm_num)
  omega

theorem main : ∀ n : ℕ,
    a (n + 1) = ((n % 2 + ∑ k ∈ Finset.range (n + 1), 4 * 5 ^ k * ((n / 5 ^ (k + 1)) % 2) : ℕ) : ℤ) := by
  sorry

end OMA.S_oeis_a093348
