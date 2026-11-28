import Mathlib

/-!
# OEIS A013936: `∑_{k ≤ n} ⌊n/k²⌋`, the error term

Source: https://oeis.org/A013936
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = ∑_{k=1}^{n} ⌊n/k²⌋`. The entry notes `a(n) = ζ(2) n + ζ(1/2) n^(1/2) + O(n^θ)` with some
`θ < 1/2`, and conjectures that `θ = 1/4 + ε` is the best possible choice.

Conventions:
* '`θ = 1/4 + ε` is best possible' is read as: for every `ε > 0` the error
  `E(n) = a(n) - ζ(2) n - ζ(1/2) √n` is `O(n^(1/4 + ε))`, and for no `ε > 0` is it
  `O(n^(1/4 - ε))`. `ζ(1/2)` is the real number `riemannZeta (1/2)` (its imaginary part is `0`).
-/

namespace OMA.S_oeis_a013936

open Asymptotics Filter

/-- `a(n) = ∑_{k=1}^{n} ⌊n/k²⌋`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, n / k ^ 2

/-- The error term. -/
noncomputable def E (n : ℕ) : ℝ :=
  a n - Real.pi ^ 2 / 6 * n - (riemannZeta (1 / 2)).re * Real.sqrt n

/-- The error exponent is exactly `1/4`. -/
theorem main :
    (∀ ε : ℝ, 0 < ε → E =O[atTop] fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 4 + ε)) ∧
    (∀ ε : ℝ, 0 < ε → ¬ E =O[atTop] fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 4 - ε)) := by
  sorry

end OMA.S_oeis_a013936
