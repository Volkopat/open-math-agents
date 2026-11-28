import Mathlib

/-!
# OEIS A056737: average order of the least gap n = k(k + m)

Source: https://oeis.org/A056737
`a n` is the minimum `m ≥ 0` such that `n = k(k + m)` for some positive integer `k`.
Conjecture (Tooth, 2025): there is a constant `k ≈ 1.7` such that `a(n)` has average order
`k n / log n`.

Conventions. "Average order `k n / log n`" is read as `∑_{n ≤ x} a(n) ~ ∑_{2 ≤ n ≤ x} k n / log n`;
`main` asserts the existence of some constant `k > 0` (the numerical value is not part of the
statement).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a056737

open Filter Asymptotics Real

/-- A056737. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | ∃ k : ℕ, 0 < k ∧ n = k * (k + m)}

theorem main :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℕ => ∑ n ∈ Finset.Icc 1 x, (a n : ℝ)) ~[atTop]
        fun x : ℕ => ∑ n ∈ Finset.Icc 2 x, c * n / log n := by
  sorry

end OMA.S_oeis_a056737
