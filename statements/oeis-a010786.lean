import Mathlib

/-!
# OEIS A010786: growth constant of the floor-factorial numbers

Source: https://oeis.org/A010786
`a n = ∏_{k=1}^{n} ⌊n/k⌋`. Kotesovec (2018): `log a(n) ~ c (n - log(2πn)/2)` with
`c = 0.7885…`; conjecture: `c = A085361 = ∑_{n ≥ 1} (ζ(n+1) - 1)/n`.

Conventions. Since `log a(n) ~ c n` alone already makes the ratio tend to `1`, the
second-order term is read as an expansion with error `o(log n)`:
`log a(n) = c (n - log(2πn)/2) + o(log n)` with `c = ∑ (ζ(n+1) - 1)/n`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a010786

open Filter Asymptotics Real

/-- The floor-factorial `∏_{k=1}^{n} ⌊n/k⌋`. -/
def a (n : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 n, n / k

/-- `c = ∑_{n ≥ 1} (ζ(n+1) - 1)/n`. -/
noncomputable def c : ℝ := ∑' n : ℕ, (riemannZeta (n + 2) - 1).re / (n + 1)

theorem main :
    (fun n : ℕ => log (a n) - c * (n - log (2 * π * n) / 2)) =o[atTop]
      fun n : ℕ => log (n : ℝ) := by
  sorry

end OMA.S_oeis_a010786
