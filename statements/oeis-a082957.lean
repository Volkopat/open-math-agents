import Mathlib

/-!
# OEIS A082957: σ(2k) < σ(2k+1)

Source: https://oeis.org/A082957
`a n` lists the `k` such that `σ(2k) < σ(2k+1)`. Conjecture: `a(n)` is asymptotic to `c n` for
some `18 < c < 18.5`.

Conventions. `k ≥ 1`, offset `1` (`Nat.nth` at `n - 1`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a082957

open Filter Asymptotics

/-- `σ(2k) < σ(2k+1)`. -/
def P (k : ℕ) : Prop :=
  1 ≤ k ∧ ∑ d ∈ (2 * k).divisors, d < ∑ d ∈ (2 * k + 1).divisors, d

theorem main :
    ∃ c : ℝ, 18 < c ∧ c < 18.5 ∧
      (fun n : ℕ => (Nat.nth P (n - 1) : ℝ)) ~[atTop] fun n : ℕ => c * n := by
  sorry

end OMA.S_oeis_a082957
