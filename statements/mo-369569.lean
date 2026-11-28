import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic

open Filter

namespace OMA.S_mo_369569

/-- The common binomial summand, with the parameters of the two series kept explicit. -/
noncomputable def summand (slope outerBase innerBase : ℝ) (n : ℕ) : ℝ :=
  (slope * n + 1) / outerBase ^ n * (Nat.choose (2 * n) n : ℝ) *
    ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * (Nat.choose (n + 2 * k) (2 * k) : ℝ) *
        (Nat.choose (2 * k) k : ℝ) * innerBase ^ (n - k)

/-- Both reciprocal-pi identities asked for in equations 1 and 2. -/
theorem main :
    let rootArgument : ℝ := 145 + 30 * Real.sqrt 6
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, summand 6 (-1728) (-324) n)
      atTop (nhds (24 / (25 * Real.pi) * Real.sqrt (375 + 120 * Real.sqrt 10))) ∧
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, summand 4 (-160) (-20) n)
      atTop (nhds (Real.sqrt 30 / (5 * Real.pi) *
        ((5 + Real.rpow rootArgument (1 / 3)) / Real.rpow rootArgument (1 / 6)))) := by
  sorry

end OMA.S_mo_369569
