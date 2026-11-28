import Mathlib

/-!
# A003722: Expansion of e.g.f. sin(sinh(x)) (odd powers only)

Source: https://oeis.org/A003722
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
For every n >= 0,
  a(n) = -2 * Sum_{k=1..∞} (-1)^k * (2*k - 1)^(2*n + 1) * BesselI(2*k - 1, 1),
where a(n) is the coefficient of x^(2*n+1) / (2*n+1)! in the Taylor expansion of sin(sinh(x)),
i.e., the (2*n+1)-th derivative of sin(sinh(x)) at x = 0.
-/

namespace OMA.S_oeis_a003722

/-- Modified Bessel function of the first kind I_ν(z) for integer order ν : ℕ. -/
noncomputable def besselI (ν : ℕ) (z : ℝ) : ℝ :=
  ∑' m : ℕ, (z / 2) ^ (2 * m + ν) / ((m.factorial : ℝ) * ((m + ν).factorial : ℝ))

/-- Conjecture: (2*n+1)-th derivative of sin(sinh(x)) at 0 equals the BesselI series. -/
theorem main :
    ∀ n : ℕ,
      iteratedDeriv (2 * n + 1) (fun x : ℝ => Real.sin (Real.sinh x)) 0 =
        -2 * ∑' k : ℕ,
          (-1 : ℝ) ^ (k + 1) * ((2 * k + 1 : ℝ) ^ (2 * n + 1)) * besselI (2 * k + 1) 1 := by
  sorry

end OMA.S_oeis_a003722
