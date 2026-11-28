import Mathlib

/-!
# A238703: floor(k*n/m) is prime for some 0 < k < n

Source: https://oeis.org/A238703

A238703 (offset 1): `a(n) = |{0 < k < n : floor(k*n/3) is prime}|`:
0, 0, 1, 1, 2, 1, 3, 3, 1, 3, 4, 0, 4, …  For example `a(4) = 1` since `floor(2*4/3) = 2` is
prime.

Conjecture (Zhi-Wei Sun, Mar 03 2014): if `n > m > 0` with `n` not divisible by `m`, then
`floor(k*n/m)` is prime for some `0 < k < n`.

Conventions: everything is in `ℕ`, and `floor(k*n/m)` is the natural-number division
`k * n / m`.
-/

namespace OMA.S_oeis_a238703

theorem main :
    ∀ n m : ℕ, 0 < m → m < n → ¬ m ∣ n →
      ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime (k * n / m) := by
  sorry

end OMA.S_oeis_a238703
