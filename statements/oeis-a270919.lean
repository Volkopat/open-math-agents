import Mathlib

/-!
# OEIS A270919

`a(n)` is the coefficient of `x^n` in `Product_{k >= 1} ((1 + x^k) / (1 - x^k))^n`.
Since `(1 + x^k) / (1 - x^k) = 1 + 2 * x^k + 2 * x^(2*k) + ...` has constant term `1` and
only factors `1 <= k <= n` contribute to `[x^n]`, we have
`a(n) = [x^n] Product_{k = 1..n} (1 + 2 * Sum_{m >= 1} x^(k * m))^n`.
(First terms: `1, 2, 12, 80, 552, 3912, 28224, 206208, ...`)

Conjecture (Peter Bala, Apr 18 2023):
The supercongruence `a(p) ≡ 2 * p + 2 (mod p^2)` holds for all odd primes `p >= 3`
(whereas for `p = 2`, `a(2) = 12 ≡ 0 ≢ 2 * 2 + 2 (mod 4)`).
-/

namespace OMA.S_oeis_a270919

/-- The power series `(1 + x^k) / (1 - x^k) = 1 + 2 * Sum_{m >= 1} x^(k * m)` in `PowerSeries ℤ`. -/
noncomputable def factorSeries (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun m => if m = 0 then 1 else if k ∣ m then 2 else 0

/-- Sequence A270919: `[x^n] Product_{k = 1..n} ((1 + x^k) / (1 - x^k))^n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∏ k ∈ Finset.Icc 1 n, (factorSeries k) ^ n)

theorem main :
    (∀ p : ℕ, p.Prime → 3 ≤ p → a p ≡ 2 * (p : ℤ) + 2 [ZMOD ((p ^ 2 : ℕ) : ℤ)]) ∧
    ¬ (a 2 ≡ 2 * (2 : ℤ) + 2 [ZMOD ((2 ^ 2 : ℕ) : ℤ)]) := by
  sorry

end OMA.S_oeis_a270919
