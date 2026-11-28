import Mathlib

/-!
# OEIS A074794: density of numbers with τ(k) ≡ 1 (mod 3)

Source: https://oeis.org/A074794
`a n` is the number of `k ≤ n` with `τ(k) ≡ 1 (mod 3)`. The density `a(n)/n` is conjecturally
`3 ζ(3) / π²` (A346602).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a074794

open Filter Topology Real

/-- A074794. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun k => k.divisors.card % 3 = 1).card

theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (3 * (riemannZeta 3).re / π ^ 2)) := by
  sorry

end OMA.S_oeis_a074794
