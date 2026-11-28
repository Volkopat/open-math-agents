import Mathlib

/-!
# OEIS A053004: AGM(1, √2) as a theta value

Source: https://oeis.org/A053004
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`AGM(1, √2)` is the common limit of `a₀ = 1, b₀ = √2, aₙ₊₁ = (aₙ + bₙ)/2, bₙ₊₁ = √(aₙ bₙ)`.
The entry records two conjectures:
* (Bala) `AGM(1, √2) = 1 / (∑_{n ∈ ℤ} exp(-π (n + 1/2)²))²`;
* `AGM(1, √2) = ∑_{k ≥ 0} A001934(k) / exp(kπ)`, where A001934 is the expansion of `1/θ₄(q)²`,
  `θ₄(q) = ∑_{n ∈ ℤ} (-1)ⁿ q^{n²}`.
`main` states both: the AGM iteration's `aₙ` converge to the first value, and the second series
sums to the same value.
-/

namespace OMA.S_oeis_a053004

open Filter Topology

/-- The AGM iteration `(aₙ, bₙ)` from `(a, b)`. -/
noncomputable def agmSeq (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | n + 1 => (((agmSeq a b n).1 + (agmSeq a b n).2) / 2,
      Real.sqrt ((agmSeq a b n).1 * (agmSeq a b n).2))

/-- `θ₄(q) = 1 + 2 ∑_{r ≥ 1} (-1)^r q^{r²}` as a formal power series over `ℚ`. -/
def theta4 : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    if m = 0 then 1 else if Nat.sqrt m * Nat.sqrt m = m then 2 * (-1) ^ Nat.sqrt m else 0

/-- A001934: coefficients of `1/θ₄(q)²`. -/
noncomputable def A001934 (k : ℕ) : ℚ := PowerSeries.coeff k ((theta4⁻¹) ^ 2)

/-- The two conjectural evaluations of `AGM(1, √2)`. -/
theorem main :
    Tendsto (fun n => (agmSeq 1 (Real.sqrt 2) n).1) atTop
        (𝓝 (1 / (∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) + 1 / 2) ^ 2)) ^ 2)) ∧
      HasSum (fun k : ℕ => (A001934 k : ℝ) / Real.exp (k * Real.pi))
        (1 / (∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) + 1 / 2) ^ 2)) ^ 2) := by
  sorry

end OMA.S_oeis_a053004
