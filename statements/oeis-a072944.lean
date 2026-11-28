import Mathlib

/-!
# A072944: Threshold N(x) for the totient recurrence f(n+1) = 2*f(n) - phi(f(n))

Source: https://oeis.org/A072944
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

For any positive integer x = f(1) > 1, let f(n+1) = 2*f(n) - phi(f(n)).
Let N(x) be the least integer such that for all n >= N(x), f(n) = 4 * f(n - 3).
Conjecture: N(x) is asymptotic to C * log(x) with 3/10 < C < 4/10.
-/

namespace OMA.S_oeis_a072944

open Filter Topology

/-- Iterated sequence starting at `f x 0 = x` with `f x (n + 1) = 2 * f x n - φ(f x n)`. -/
def f (x : ℕ) : ℕ → ℕ
  | 0 => x
  | n + 1 => 2 * f x n - Nat.totient (f x n)

/-- Least `M ≥ 4` such that for all `n ≥ M`, `f x (n - 1) = 4 * f x (n - 4)`. -/
noncomputable def N (x : ℕ) : ℕ :=
  sInf { M : ℕ | 4 ≤ M ∧ ∀ n : ℕ, M ≤ n → f x (n - 1) = 4 * f x (n - 4) }

theorem main :
    ∃ C : ℝ, (3 : ℝ) / 10 < C ∧ C < (4 : ℝ) / 10 ∧
      Tendsto (fun x : ℕ => (N x : ℝ) / (C * Real.log (x : ℝ))) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a072944
