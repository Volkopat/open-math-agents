import Mathlib

/-!
# OEIS A380680: Expansion of `∑_{m=-∞}^{∞} x^(m^2) * (2 - x^m)^m / (1 - 2*x^m)^m`

Source: https://oeis.org/A380680 (OEIS Foundation, CC BY-SA 4.0).
Since the summand `x^(m^2) * (2 - x^m)^m / (1 - 2*x^m)^m` is invariant under `m ↦ -m`,
`A(x) = 1 + 2 * ∑_{m ≥ 1} x^(m^2) * (2 - x^m)^m / (1 - 2*x^m)^m`.

Conjecture (Paul D. Hanna, OEIS A380680):
For every `n > 0`, `a(n) ≡ 2 (mod 4)` iff `n` is a square, and `4 ∣ a(n)` when `n` is nonsquare.
-/

namespace OMA.S_oeis_a380680

/-- The formal power series `1 / (1 - 2 * X^m) = ∑_{j ≥ 0} (2 * X^m)^j` in `PowerSeries ℤ`. -/
noncomputable def invOneSubTwoXpow (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => if m ∣ k then (2 : ℤ) ^ (k / m) else 0

/-- The `m`-th positive summand `X^(m^2) * (2 - X^m)^m / (1 - 2*X^m)^m` for `m ≥ 1`. -/
noncomputable def term (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ (m ^ 2) * (2 - PowerSeries.X ^ m) ^ m * (invOneSubTwoXpow m) ^ m

/-- OEIS A380680: `[x^n] (1 + 2 * ∑_{m ≥ 1} term m)`.
Terms with `m > n` have `m^2 > n` and contribute `0` to the `n`-th coefficient. -/
noncomputable def A380680 (n : ℕ) : ℤ :=
  (if n = 0 then 1 else 0) + 2 * ∑ m ∈ Finset.Icc 1 n, (term m).coeff n

/-- Conjecture (OEIS A380680):
For every `n ≥ 1`, `A380680 n % 4 = 2` iff `n` is a square, and `4 ∣ A380680 n` if `n` is not a square. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (A380680 n % 4 = 2 ↔ IsSquare n) ∧ (¬ IsSquare n → (4 : ℤ) ∣ A380680 n) := by
  sorry

end OMA.S_oeis_a380680
