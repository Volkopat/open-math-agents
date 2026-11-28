import Mathlib

/-!
# OEIS A292180: G.f. `∑_{m=-∞}^∞ (1 + x^m)^m / (1 - x^m)^m` (ignoring constant term)

Source: https://oeis.org/A292180 (OEIS Foundation, CC BY-SA 4.0).
Pairing `+m` and `-m` for `m ≥ 1` (since `(1 + x^(-m))^(-m) / (1 - x^(-m))^(-m) = (-1)^m * (1 - x^m)^m / (1 + x^m)^m`),
the `k`-th coefficient for `k ≥ 1` is
`a(k) = ∑_{m ∣ k} [u^(k/m)] ((1 + u)^m / (1 - u)^m + (-1)^m * (1 - u)^m / (1 + u)^m)`.

Conjecture (Paul D. Hanna, OEIS A292180):
For every `n ≥ 1`, `a((2*n - 1)^2) / 4` is odd (and `4 ∣ a((2*n - 1)^2)`).
-/

namespace OMA.S_oeis_a292180

/-- Formal power series `1 / (1 - X) = ∑_{j ≥ 0} X^j` in `PowerSeries ℤ`. -/
noncomputable def invOneSubX : PowerSeries ℤ :=
  PowerSeries.mk fun _ => 1

/-- Formal power series `1 / (1 + X) = ∑_{j ≥ 0} (-1)^j X^j` in `PowerSeries ℤ`. -/
noncomputable def invOneAddX : PowerSeries ℤ :=
  PowerSeries.mk fun j => (-1 : ℤ) ^ j

/-- The `m`-th paired base series `F_m(u) = (1 + u)^m / (1 - u)^m + (-1)^m * (1 - u)^m / (1 + u)^m`. -/
noncomputable def pairSeries (m : ℕ) : PowerSeries ℤ :=
  (1 + PowerSeries.X) ^ m * invOneSubX ^ m +
    (-1 : PowerSeries ℤ) ^ m * (1 - PowerSeries.X) ^ m * invOneAddX ^ m

/-- OEIS A292180: for `k ≥ 1`, `a(k) = ∑_{m ∣ k} (pairSeries m).coeff (k / m)`. -/
noncomputable def A292180 (k : ℕ) : ℤ :=
  ∑ m ∈ k.divisors, (pairSeries m).coeff (k / m)

/-- Conjecture (OEIS A292180):
For every `n ≥ 1`, `4 ∣ A292180 ((2 * n - 1) ^ 2)` and `Odd (A292180 ((2 * n - 1) ^ 2) / 4)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (4 : ℤ) ∣ A292180 ((2 * n - 1) ^ 2) ∧ Odd (A292180 ((2 * n - 1) ^ 2) / 4) := by
  sorry

end OMA.S_oeis_a292180
