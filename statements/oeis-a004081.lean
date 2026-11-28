import Mathlib

/-!
# A004081: Positive integers m with exactly one integer between exp(H_m) and exp(H_{m+1})

Source: https://oeis.org/A004081
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture (David W. Cantrell, Aug 11 2007):
Let s(m) = 1 + 1/2 + ... + 1/m be the m-th harmonic number, and let a(n) be the n-th positive
integer m such that exactly one integer lies strictly between exp(s(m)) and exp(s(m+1)).
Then for all n >= 1,
  a(n) = floor(n / (2 - exp(γ)) - 1/2 + exp(γ) / (24*n)),
where γ is the Euler-Mascheroni constant.
-/

namespace OMA.S_oeis_a004081

open Filter

/-- The m-th harmonic number H_m = Sum_{k=1..m} 1/k. -/
noncomputable def harmonicReal (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)

/-- The Euler-Mascheroni constant γ = lim_{m -> ∞} (H_m - log m). -/
noncomputable def eulerGamma : ℝ :=
  limUnder atTop (fun m : ℕ => harmonicReal m - Real.log (m : ℝ))

/-- Predicate that m >= 1 has exactly one integer strictly between exp(H_m) and exp(H_{m+1}). -/
def isGood (m : ℕ) : Prop :=
  1 ≤ m ∧
  {k : ℤ | Real.exp (harmonicReal m) < (k : ℝ) ∧ (k : ℝ) < Real.exp (harmonicReal (m + 1))}.ncard = 1

/-- The n-th positive integer (1-indexed) satisfying isGood. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth isGood (n - 1)

/-- Conjectured exact floor formula for A004081. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℤ) =
        Int.floor
          ((n : ℝ) / (2 - Real.exp eulerGamma) - 1 / 2 +
            Real.exp eulerGamma / (24 * (n : ℝ))) := by
  sorry

end OMA.S_oeis_a004081
