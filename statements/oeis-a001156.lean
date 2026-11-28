import Mathlib

/-!
# Asymptotics of the number of partitions into squares (A001156)

Source: https://oeis.org/A001156
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of partitions of `n` into squares. Conjecture (Bohman, Fröberg, Riesel,
1979): `a(n) ~ c · n^(-α) · exp(β n^(1/3))` with `c = 1/18.79656`, `β = 3.30716`,
`α = 1.16022`.

Conventions:
* `a(n)` counts `Nat.Partition n` all of whose parts are perfect squares.
* The constants are given to five decimals, so `main` asks for constants `c, α, β` agreeing
  with the stated decimals up to rounding (`|1/c - 18.79656|, |β - 3.30716|, |α - 1.16022|` all
  at most `5·10⁻⁶`) for which `a(n) / (c n^(-α) exp(β n^(1/3))) → 1`.
-/

namespace OMA.S_oeis_a001156

open Filter

/-- Number of partitions of `n` into squares. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun P => ∀ i ∈ P.parts, IsSquare i).card

theorem main :
    ∃ c α β : ℝ, 0 < c ∧ |1 / c - 18.79656| ≤ 5e-6 ∧ |β - 3.30716| ≤ 5e-6 ∧
      |α - 1.16022| ≤ 5e-6 ∧
      Tendsto (fun n : ℕ => (a n : ℝ) /
        (c * (n : ℝ) ^ (-α) * Real.exp (β * (n : ℝ) ^ ((1 : ℝ) / 3)))) atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a001156
