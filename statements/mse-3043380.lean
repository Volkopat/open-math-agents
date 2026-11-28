import Mathlib

/-!
# Is there a substitution transforming every Fermat curve into an elliptic curve?

Source: https://math.stackexchange.com/questions/3043380/is-there-a-substitution-which-transforms-every-fermat-curve-into-an-elliptic-cur
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

For degree `n = 3` and `n = 4`, rational substitutions transform the Fermat curve
`x^n + y^n = z^n` into a Weierstrass elliptic curve `b^2 = a^3 + A a + B`.
Question: For every integer `n ≥ 3`, is there a nonconstant rational substitution
transforming the affine Fermat curve `x^n + y^n = 1` into a nonsingular Weierstrass
elliptic curve `b^2 = a^3 + A a + B` over `ℝ`?

Conventions:
- The rational substitution is given by pairs of bivariate real polynomials
  `(Pa, Qa)` and `(Pb, Qb)` representing `a(x, y) = Pa(x, y) / Qa(x, y)` and
  `b(x, y) = Pb(x, y) / Qb(x, y)`.
- Nonsingularity of `b^2 = a^3 + A a + B` is `4 A^3 + 27 B^2 ≠ 0`.
- Nonconstancy requires `a(x, y)` to take at least two distinct values on the curve.
- `Qb` must be nonzero at some real point of the curve, so the curve identity is not vacuous.
-/

namespace OMA.S_mse_3043380

theorem main :
    ∀ n : ℕ, 3 ≤ n →
      ∃ (A B : ℝ) (Pa Qa Pb Qb : MvPolynomial (Fin 2) ℝ),
        4 * A ^ 3 + 27 * B ^ 2 ≠ 0 ∧
        (∀ x y : ℝ, x ^ n + y ^ n = 1 →
          MvPolynomial.eval ![x, y] Qa ≠ 0 →
          MvPolynomial.eval ![x, y] Qb ≠ 0 →
          (MvPolynomial.eval ![x, y] Pb / MvPolynomial.eval ![x, y] Qb) ^ 2 =
            (MvPolynomial.eval ![x, y] Pa / MvPolynomial.eval ![x, y] Qa) ^ 3 +
            A * (MvPolynomial.eval ![x, y] Pa / MvPolynomial.eval ![x, y] Qa) + B) ∧
        (∃ x₁ y₁ x₂ y₂ : ℝ,
          x₁ ^ n + y₁ ^ n = 1 ∧ x₂ ^ n + y₂ ^ n = 1 ∧
          MvPolynomial.eval ![x₁, y₁] Qa ≠ 0 ∧ MvPolynomial.eval ![x₂, y₂] Qa ≠ 0 ∧
          MvPolynomial.eval ![x₁, y₁] Qb ≠ 0 ∧
          MvPolynomial.eval ![x₁, y₁] Pa / MvPolynomial.eval ![x₁, y₁] Qa ≠
            MvPolynomial.eval ![x₂, y₂] Pa / MvPolynomial.eval ![x₂, y₂] Qa) := by
  sorry

end OMA.S_mse_3043380
