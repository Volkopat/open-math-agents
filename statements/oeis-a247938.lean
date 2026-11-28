import Mathlib

/-!
# A247938: Sum of divisors of 2^prime(n)-1.

Source: https://oeis.org/A247938
Credit: @divmxnd0x

Conjecture (Jianing Song, Dec 31 2022, stated in A247938): `a(n)/2^prime(n)` reaches its maximum
value `135/128` at `n = 5`.

Formalization notes:
* `prime n` is the `n`-th prime (`prime 1 = 2`) and `a n = sigma(2^prime(n) - 1)`; the ratio
  `a(n)/2^prime(n)` is taken in `ℚ`. At `n = 5`, `2^11 - 1 = 23 · 89` and `a(5) = 2160`, so the
  ratio is `2160/2048 = 135/128`.
* The conjecture: `135/128` is the greatest value of the ratio over `n ≥ 1`, attained at `n = 5`.
-/

namespace OMA.S_oeis_a247938

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `a(n)/2^prime(n)` with `a(n) = sigma(2^prime(n) - 1)`. -/
noncomputable def ratio (n : ℕ) : ℚ :=
  (ArithmeticFunction.sigma 1 (2 ^ prime n - 1) : ℚ) / 2 ^ prime n

/-- The ratio is maximal at `n = 5`, with value `135/128`. -/
theorem main : IsGreatest {x : ℚ | ∃ n : ℕ, 1 ≤ n ∧ x = ratio n} (135 / 128) ∧
    ratio 5 = 135 / 128 := by
  sorry

end OMA.S_oeis_a247938
