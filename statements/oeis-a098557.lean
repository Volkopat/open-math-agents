import Mathlib

/-!
# A098557: Expansion of e.g.f. (1/2)*(1+x)*log((1+x)/(1-x))

Source: https://oeis.org/A098557
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Expansion of e.g.f. (1/2)*(1+x)*log((1+x)/(1-x)).
Conjecture: -a(n) + a(n-1) + (n-1)*(n-3)*a(n-2) = 0.
-/

namespace OMA.S_oeis_a098557

noncomputable def polyTrunc (n : ℕ) : Polynomial ℚ :=
  (1 + Polynomial.X) *
    ∑ k ∈ Finset.range (n + 1), (((2 * k + 1 : ℚ)⁻¹) • (Polynomial.X ^ (2 * k + 1)))

noncomputable def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * (polyTrunc n).coeff n

theorem main :
    ∀ n : ℕ, 3 ≤ n →
      -a n + a (n - 1) + ((n : ℚ) - 1) * ((n : ℚ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a098557
