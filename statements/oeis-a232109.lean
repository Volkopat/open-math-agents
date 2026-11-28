import Mathlib

/-!
# A232109: Least prime p < n + 5 with n + (p-1)*(p-3)/8 prime, or 0 if such a prime p does not exist.

Source: https://oeis.org/A232109
Credit: @sntntHb

Data: 5, 3, 3, 5, 3, 5, 3, 7, 11, 5, 3, 5, 3, 7, 17, 5, 3, 5, 3, 7, ...

Conjecture (Zhi-Wei Sun, stated on the OEIS page): `a(n) > 0` for all `n > 0`, i.e. for every
`n ≥ 1` there is a prime `p < n + 5` such that `n + (p-1)*(p-3)/8` is prime.

Conventions:
- For `p = 2` the quantity `(p-1)*(p-3)/8 = -1/8` is not an integer, so `p = 2` never qualifies
  (the OEIS program tests `PrimeQ` on a non-integer); we therefore require `p ≠ 2`.
- For odd `p`, `(p-1)*(p-3)` is divisible by `8`, so natural-number division is exact.
-/

namespace OMA.S_oeis_a232109

theorem main :
    ∀ n : ℕ, 0 < n → ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p < n + 5 ∧
      (n + (p - 1) * (p - 3) / 8).Prime := by
  sorry

end OMA.S_oeis_a232109
