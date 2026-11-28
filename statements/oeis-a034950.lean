import Mathlib

/-!
# A034950: Expansion of eta(8z)*eta(16z)*theta_3(2z)

Source: https://oeis.org/A034950
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
Sum_{k=1..n} a(k)^2 ~ c * n^(3/2), where c = 0.787...

Conventions:
In q-series (q = exp(2*pi*i*z)),
  eta(8z) * eta(16z) * theta_3(2z)
  = q * (Prod_{m >= 1} (1 - q^(8*m)) * (1 - q^(16*m))) * (1 + 2 * Sum_{m >= 1} q^(2*m^2)).
For each n, the coefficient a(n) depends only on factors with degree <= n, so it is computed
exactly as the n-th coefficient of the truncated polynomial in Polynomial ℤ.
-/

namespace OMA.S_oeis_a034950

open Polynomial Filter

/-- The n-th coefficient of q * (Prod_{m >= 1} (1 - q^(8*m))(1 - q^(16*m))) * (Sum_{m in ℤ} q^(2*m^2)). -/
noncomputable def a (n : ℕ) : ℤ :=
  let etaProd : ℤ[X] :=
    ∏ m ∈ Finset.Icc 1 n, (1 - X ^ (8 * m)) * (1 - X ^ (16 * m))
  let thetaPart : ℤ[X] :=
    1 + 2 * ∑ m ∈ Finset.Icc 1 n, X ^ (2 * m ^ 2)
  (X * etaProd * thetaPart).coeff n

/-- Conjecture: Sum_{k=1..n} a(k)^2 ~ c * n^(3/2) for a positive constant c ≈ 0.787. -/
theorem main :
    ∃ c : ℝ, 0 < c ∧
      Tendsto
        (fun n : ℕ =>
          (∑ k ∈ Finset.Icc 1 n, ((a k : ℝ) ^ 2)) / ((n : ℝ) ^ ((3 : ℝ) / 2)))
        atTop (nhds c) := by
  sorry

end OMA.S_oeis_a034950
