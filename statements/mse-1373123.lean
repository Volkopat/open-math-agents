import Mathlib

/-!
# A conjectured identity for tetralogarithms `Li₄`

Source: https://math.stackexchange.com/questions/1373123
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (asker, found by PSLQ):
`720 Li₄(1/2) - 2160 Li₄(1/3) + 2160 Li₄(2/3) + 270 Li₄(1/4) + 540 Li₄(3/4) + 135 Li₄(1/9)
  = 19π⁴ + 30(π² - β²)(10α² - 12αβ + 3β²) - 30α²(19α² - 24αβ + 8β²)`, `α = ln 2`, `β = ln 3`.

Conventions:
* `Li₄(x) = ∑_{n ≥ 1} xⁿ/n⁴` (a `tsum`; all arguments lie in `(0, 1)`, where it converges).
-/

namespace OMA.S_mse_1373123

/-- The tetralogarithm on `(0, 1)`. -/
noncomputable def Li4 (x : ℝ) : ℝ := ∑' n : ℕ, x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 4

/-- The conjectured identity. -/
theorem main :
    let α := Real.log 2
    let β := Real.log 3
    720 * Li4 (1 / 2) - 2160 * Li4 (1 / 3) + 2160 * Li4 (2 / 3) + 270 * Li4 (1 / 4) +
        540 * Li4 (3 / 4) + 135 * Li4 (1 / 9) =
      19 * Real.pi ^ 4 + 30 * (Real.pi ^ 2 - β ^ 2) * (10 * α ^ 2 - 12 * α * β + 3 * β ^ 2) -
        30 * α ^ 2 * (19 * α ^ 2 - 24 * α * β + 8 * β ^ 2) := by
  sorry

end OMA.S_mse_1373123
