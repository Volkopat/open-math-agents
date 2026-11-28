import Mathlib

/-!
# A331343: a(n) = lcm(1,2,...,n) * Sum_{k=1..n} (2^(k-1) - 1) / k.

Source: https://oeis.org/A331343
Credit: @ceejcake

Formalizes the OEIS A331343 conjecture (offset 1):
For `n > 3`, if `n^3 | a(n)`, then `n` is prime.

Conventions:
* `a n` is defined directly in `ℕ` as
  `∑ k ∈ Finset.Icc 1 n, ((Finset.Icc 1 n).lcm id / k) * (2 ^ (k - 1) - 1)`.
  For every `k ∈ Finset.Icc 1 n`, `k` divides `(Finset.Icc 1 n).lcm id` and `2 ^ (k - 1) ≥ 1`,
  so each division and subtraction is exact and `a n` equals `lcm(1, ..., n) * ∑_{k=1}^n (2^(k-1) - 1) / k`
  in `ℚ`.
* Initial values agree with OEIS A331343 (offset 1):
  `a 1 = 0`, `a 2 = 1`, `a 3 = 9`, `a 4 = 39`, `a 5 = 375`, `a 6 = 685`, `a 7 = 8575`,
  `a 8 = 30485`, `a 9 = 162855`, `a 10 = 291627`.
-/

namespace OMA.S_oeis_a331343

/-- `a n = lcm(1, 2, ..., n) * ∑_{k=1}^n (2^(k-1) - 1) / k`, computed exactly in `ℕ`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, ((Finset.Icc 1 n).lcm id / k) * (2 ^ (k - 1) - 1)

/-- Conjecture (OEIS A331343): for every `n > 3`, if `n^3 ∣ a n`, then `n` is prime. -/
theorem main : ∀ n : ℕ, 3 < n → n ^ 3 ∣ a n → n.Prime := by
  sorry

end OMA.S_oeis_a331343
