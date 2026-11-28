import Mathlib

/-!
# OEIS A002285: `log₁₀ e` from digit counts of harmonic numbers

Source: https://oeis.org/A002285
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Weisstein): `log₁₀ e = lim_{n → ∞} b(n)/10^(n-1)` for `b = A114467` or `b = A114468`,
the numbers of decimal digits of the numerator, resp. denominator, of the `10ⁿ`-th harmonic number.
More generally, `log_k e = lim_{n → ∞} ⌊log_k b(kⁿ)⌋ / k^(n-1)` for `b = A001008` or `A002805`
(numerators, resp. denominators, of `H(m)`) and every `k ≥ 2`.

Conventions:
* `H(m) = ∑_{i=1}^{m} 1/i` in lowest terms (`Rat.num`, `Rat.den`). Decimal digit counts are
  `(Nat.digits 10 ·).length`; `⌊log_k x⌋` for `x ≥ 1` is `Nat.log k x`.
* `main` states the base-10 digit version and the general version.
-/

namespace OMA.S_oeis_a002285

open Filter Topology

/-- The harmonic number `H(m)`. -/
def H (m : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 m, (1 : ℚ) / i

/-- Both versions of Weisstein's conjecture. -/
theorem main :
    Tendsto (fun n : ℕ => ((Nat.digits 10 (H (10 ^ n)).num.natAbs).length : ℝ) / 10 ^ ((n : ℝ) - 1))
      atTop (𝓝 (Real.logb 10 (Real.exp 1))) ∧
    Tendsto (fun n : ℕ => ((Nat.digits 10 (H (10 ^ n)).den).length : ℝ) / 10 ^ ((n : ℝ) - 1))
      atTop (𝓝 (Real.logb 10 (Real.exp 1))) ∧
    ∀ k : ℕ, 2 ≤ k →
      Tendsto (fun n : ℕ => (Nat.log k (H (k ^ n)).num.natAbs : ℝ) / (k : ℝ) ^ ((n : ℝ) - 1))
        atTop (𝓝 (Real.logb k (Real.exp 1))) ∧
      Tendsto (fun n : ℕ => (Nat.log k (H (k ^ n)).den : ℝ) / (k : ℝ) ^ ((n : ℝ) - 1))
        atTop (𝓝 (Real.logb k (Real.exp 1))) := by
  sorry

end OMA.S_oeis_a002285
