import Mathlib

namespace OMA.S_oeis_a270924

open PowerSeries BigOperators

/-- Formal power series `1 / (1 - X^k) = ∑_{j ≥ 0} X^(k*j)` in `ℕ[[X]]` for `k ≥ 1`. -/
noncomputable def invOneSubPow (k : ℕ) : PowerSeries ℕ :=
  PowerSeries.mk fun m => if k ∣ m then 1 else 0

/-- The `k`-th factor `((1 + X^k) / (1 - X^k))^k` in `ℕ[[X]]`. -/
noncomputable def prodFactor (k : ℕ) : PowerSeries ℕ :=
  ((1 + PowerSeries.X ^ k) * invOneSubPow k) ^ k

/-- Truncated product `∏_{k=1}^N ((1 + X^k) / (1 - X^k))^k` in `ℕ[[X]]`,
which agrees with `∏_{k ≥ 1} ((1 + X^k) / (1 - X^k))^k` through degree `N`. -/
noncomputable def prodTrunc (N : ℕ) : PowerSeries ℕ :=
  ∏ k ∈ Finset.Icc 1 N, prodFactor k

/-- The infinite product `F(X) = ∏_{k ≥ 1} ((1 + X^k) / (1 - X^k))^k` in `ℕ[[X]]`. -/
noncomputable def prodSeries : PowerSeries ℕ :=
  PowerSeries.mk fun m => PowerSeries.coeff m (prodTrunc m)

/-- Sequence OEIS A270924: `a(n) = [x^n] ∏_{k ≥ 1} ((1 + x^k) / (1 - x^k))^(k * n)`. -/
noncomputable def a270924 (n : ℕ) : ℕ :=
  PowerSeries.coeff n (prodSeries ^ n)

/-- Conjecture on OEIS A270924 (Peter Bala, Apr 18 2023):
The Gauss congruences `a(n * p^k) ≡ a(n * p^(k - 1)) (mod p^k)` hold for all
primes `p` and all positive integers `n` and `k`. -/
theorem main :
    ∀ (p n k : ℕ), p.Prime → 1 ≤ n → 1 ≤ k →
      ((p ^ k : ℕ) : ℤ) ∣ ((a270924 (n * p ^ k) : ℤ) - (a270924 (n * p ^ (k - 1)) : ℤ)) := by
  sorry

end OMA.S_oeis_a270924
