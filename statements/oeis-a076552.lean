import Mathlib

/-!
# A076552: a(n) = (-1)^(n+1)/3/(2n+1) * Sum_{k=0..n} 16^k*B(2k)*C(2n+1,2k) where B(k) denotes the k-th Bernoulli number.

Source: https://oeis.org/A076552
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: a(n) = -1/3*(-4)^n*E(2*n,-1/2), where E(n,x) is the n-th Euler polynomial.
-/

namespace OMA.S_oeis_a076552

/-- The sequence `a(n) = (-1)^(n+1) / (3*(2n+1)) * ∑_{k=0..n} 16^k * B(2k) * C(2n+1, 2k)`. -/
noncomputable def a (n : ℕ) : ℚ :=
  ((-1 : ℚ) ^ (n + 1) / (3 * (2 * n + 1 : ℚ))) *
    ∑ k ∈ Finset.range (n + 1),
      (16 : ℚ) ^ k * bernoulli (2 * k) * ((2 * n + 1).choose (2 * k) : ℚ)

/-- The `m`-th Euler polynomial `E_m(x)`, defined by `E_m(x + 1) + E_m(x) = 2 * x^m`. -/
noncomputable def eulerPoly : ℕ → Polynomial ℚ
  | m => Polynomial.X ^ m - (1 / 2 : ℚ) • ∑ k : Fin m, (m.choose k.1 : ℚ) • eulerPoly k.1
  decreasing_by exact k.isLt

/-- Conjecture: `a(n) = -(1/3) * (-4)^n * E_{2n}(-1/2)` for all `n`. -/
theorem main :
    ∀ n : ℕ, a n = -(1 / 3 : ℚ) * (-4 : ℚ) ^ n * (eulerPoly (2 * n)).eval (-(1 / 2 : ℚ)) := by sorry

end OMA.S_oeis_a076552
