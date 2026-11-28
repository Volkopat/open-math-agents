import Mathlib

/-!
# OEIS A045575: Largest d-Digit Number of the Form x^y - y^x

Source: https://oeis.org/A045575
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Consider nonnegative integers of the form $x^y - y^x$ for integers $x, y > 1$.

Conjecture: For every $d > 11$, $10^d - d^{10}$ is the largest base-10 $d$-digit term;
that is, for all $x, y > 1$, if $10^{d-1} \le x^y - y^x < 10^d$ (with $y^x \le x^y$),
then $x^y - y^x \le 10^d - d^{10}$.
-/

namespace OMA.S_oeis_a045575

theorem main :
    ∀ d x y : ℕ, 11 < d → 1 < x → 1 < y →
      y ^ x ≤ x ^ y →
      10 ^ (d - 1) ≤ x ^ y - y ^ x →
      x ^ y - y ^ x < 10 ^ d →
      x ^ y - y ^ x ≤ 10 ^ d - d ^ 10 := by
  sorry

end OMA.S_oeis_a045575
