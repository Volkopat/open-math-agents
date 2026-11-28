import Mathlib

/-!
# OEIS A111000: ratio of consecutive values of ζ(ζ(n))

Source: https://oeis.org/A111000 (`a n = ⌊ζ(ζ(n))⌋`)
Conjecture on the entry: `lim_{n → ∞} ζ(ζ(n)) / ζ(ζ(n+1)) = 1/2`.

Conventions. `ζ` is Mathlib's `riemannZeta`; for integers `n ≥ 2`, `ζ(n)` is real and `> 1`, so
`ζ(ζ(n))` is evaluated at the real number `ζ(n)` and is real; real parts are taken.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a111000

open Filter Topology

/-- `ζ(ζ(n))` as a real number. -/
noncomputable def zz (n : ℕ) : ℝ := (riemannZeta ((riemannZeta n).re : ℂ)).re

theorem main : Tendsto (fun n : ℕ => zz n / zz (n + 1)) atTop (𝓝 (1 / 2)) := by
  sorry

end OMA.S_oeis_a111000
