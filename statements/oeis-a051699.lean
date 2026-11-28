import Mathlib

/-!
# OEIS A051699: summatory distance to the nearest prime

Source: https://oeis.org/A051699
`a n` is the distance from `n` to the closest prime. Conjecture:
`S(n) = ∑_{k=1}^{n} a(k)` is asymptotic to `C n log n` with `C = 0.29…`.
`main` states that `S(n) ~ C n log n` for some constant `C > 0` (the numerical value is
not part of the statement).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a051699

open Filter Asymptotics Real

/-- Distance from `n` to the nearest prime. -/
noncomputable def a (n : ℕ) : ℕ := sInf {d | (n + d).Prime ∨ (d ≤ n ∧ (n - d).Prime)}

theorem main :
    ∃ C : ℝ, 0 < C ∧
      (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (a k : ℝ))) ~[atTop] fun n => C * n * log n := by
  sorry

end OMA.S_oeis_a051699
