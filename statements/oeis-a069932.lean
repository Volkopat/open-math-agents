import Mathlib

/-!
# A069932: Asymptotic average order of |{1 <= k <= n : phi(k) | n}|

Source: https://oeis.org/A069932
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A069932: Number of k, 1 <= k <= n, such that phi(k) divides n.

Statement:
Asymptotically (still conjectured): Sum_{k=1..n} a(k) = C*n*log(n) + o(n*log(n))
with C = 1.5...

Conventions:
- Formalized as the existence of a positive constant `C > 0` such that
  `(Sum_{k=1..n} a(k)) / (n * log n) -> C` as `n -> infinity`.
-/

namespace OMA.S_oeis_a069932

/-- `A069932(n)`: number of `k` in `1..n` such that `phi(k) | n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => Nat.totient k ∣ n)).card

theorem main :
    ∃ C : ℝ, 0 < C ∧
      Filter.Tendsto
        (fun n : ℕ =>
          ((∑ k ∈ Finset.Icc 1 n, (a k : ℝ))) / ((n : ℝ) * Real.log (n : ℝ)))
        Filter.atTop (nhds C) := by
  sorry

end OMA.S_oeis_a069932
