import Mathlib

/-!
# A curious series related to the asymptotic behavior of the tetration

Source: https://mathoverflow.net/questions/260379/a-curious-series-related-to-the-asymptotic-behavior-of-the-tetration
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For `1 < a < e^(1/e)` put `λ = -W(-ln a) ∈ (0, 1)`, so that `ln a = λ e^(-λ)`. The tetration
`ⁿa` (`⁰a = 1`, `ⁿ⁺¹a = a^(ⁿa)`) satisfies `ⁿa = e^λ - c_λ λ^n + O(λ^(2n))`. The question asks
whether `λ ↦ c_λ` is unimodal on `(0, 1)`, as its graph suggests (and where its maximum is, and
whether its series can be summed). `main` states the positive answer to the unimodality
question; a proof of its negation answers no.

Conventions:
* `a = exp(λ e^(-λ))` parametrises `1 < a < e^(1/e)` by `λ ∈ (0, 1)` (this inverts
  `λ = -W(-ln a)` on the principal branch).
* `c_λ = lim_{n → ∞} (e^λ - ⁿa) / λ^n` (the limit exists by the stated asymptotics).
* Unimodal: for some `μ ∈ (0, 1)`, `c` is monotone on `(0, μ]` and antitone on `[μ, 1)`.
-/

namespace OMA.S_mo_260379

open Filter Topology

/-- The tetration `ⁿa`. -/
noncomputable def tet (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => a ^ tet a n

/-- The base corresponding to `λ`. -/
noncomputable def base (l : ℝ) : ℝ := Real.exp (l * Real.exp (-l))

/-- `c_λ`. -/
noncomputable def c (l : ℝ) : ℝ :=
  limUnder atTop fun n : ℕ => (Real.exp l - tet (base l) n) / l ^ n

theorem main :
    ∃ μ ∈ Set.Ioo (0 : ℝ) 1, MonotoneOn c (Set.Ioc 0 μ) ∧ AntitoneOn c (Set.Ico μ 1) := by
  sorry

end OMA.S_mo_260379
