import Mathlib

/-!
# A081362: Series evaluation for q^(1/24) * eta(q) / eta(q^2) at q = exp(-Pi)

Source: https://oeis.org/A081362
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A081362: Expansion of q^(1/24) * eta(q) / eta(q^2) in powers of q.

Statement:
Conjecture: Sum_{k>=0} a(k) / exp(k*Pi) = exp(-1/24*Pi) * 2^(1/8).

Conventions:
- `q^(1/24) * eta(q) / eta(q^2) = Product_{m >= 1} (1 - q^m) / (1 - q^(2m)) = Product_{m >= 1} 1 / (1 + q^m)`.
- Thus `a(k)` is the coefficient `[x^k] Product_{m=1..k} (1 / (1 + x^m))` in `PowerSeries ℤ`
  (equivalently, `Sum_{p ∈ Partitions k} (-1)^(p.parts.card)` when expanded via `1/(1+x^m) = 1 - x^m + x^(2m) - ...`).
-/

namespace OMA.S_oeis_a081362

/-- The `k`-th coefficient of `Product_{m >= 1} 1 / (1 + x^m)` (`A081362`). -/
noncomputable def a (k : ℕ) : ℤ :=
  PowerSeries.coeff k
    (∏ m ∈ Finset.Icc 1 k,
      PowerSeries.mk (fun j => if m ∣ j then (-1 : ℤ) ^ (j / m) else 0))

theorem main :
    ∑' (k : ℕ), (a k : ℝ) / Real.exp ((k : ℝ) * Real.pi) =
      Real.exp (-(1 / 24 : ℝ) * Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 8) := by
  sorry

end OMA.S_oeis_a081362
