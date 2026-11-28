import Mathlib

/-!
# A195986: Exponent of the largest power of 2 that divides 5^n - 3^n.

Source: https://oeis.org/A195986
Credit: @bnb9001

Both sequences have offset 1. `a n` is the 2-adic valuation of `5 ^ n - 3 ^ n`, and `b n` is the
2-adic valuation of `3 ^ n - 1` (OEIS A090740, the exponent of 2 in 3^n - 1).

Conjecture: a(n) = 1 if A090740(n) = 1, else a(n) = A090740(n) + 1. Amiram Eldar notes that
the conjecture is true.
-/

namespace OMA.S_oeis_a195986

/-- The exponent of the largest power of 2 dividing `5 ^ n - 3 ^ n` (A195986). -/
def a (n : ℕ) : ℕ := padicValNat 2 (5 ^ n - 3 ^ n)

/-- The exponent of 2 in `3 ^ n - 1` (A090740). -/
def b (n : ℕ) : ℕ := padicValNat 2 (3 ^ n - 1)

/-- For every `n ≥ 1`, `a n = 1` if `b n = 1`, and `a n = b n + 1` otherwise. -/
theorem main : ∀ n ≥ 1, a n = if b n = 1 then 1 else b n + 1 := by
  sorry

end OMA.S_oeis_a195986
