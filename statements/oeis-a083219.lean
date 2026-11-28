import Mathlib

/-!
# A083219: a(n) = n - 2*floor(n/4).

Source: https://oeis.org/A083219
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: number of roots of P(x) = x^n - x^(n-1) - x^(n-2) - ... - x - 1 in the left half-plane.
-/

namespace OMA.S_oeis_a083219

noncomputable def poly (d : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ d - ∑ k ∈ Finset.range d, Polynomial.X ^ k

theorem main :
    ∀ n : ℕ,
      (by
        classical
        exact ((poly (n + 1)).roots.filter (fun z : ℂ => z.re < 0)).card) =
        n - 2 * (n / 4) := by
  sorry

end OMA.S_oeis_a083219
