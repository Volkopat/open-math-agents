import Mathlib

/-!
# OEIS A070077: gcd of the n-th squarefree and n-th cubefree numbers

Source: https://oeis.org/A070077
`a n = gcd(n-th squarefree number, n-th cubefree number)`. Conjecture: every squarefree `k`
occurs as a value, i.e. for every squarefree `k` there is `m` with `a(m) = k`.

Conventions. Squarefree and cubefree numbers are positive integers; both lists are indexed
from `1` (`Nat.nth` at `m - 1`). A number is cubefree if no `p³` divides it.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a070077

/-- `n ≥ 1` is cubefree. -/
def IsCubefree (n : ℕ) : Prop := 1 ≤ n ∧ ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ n

/-- A070077. -/
noncomputable def a (m : ℕ) : ℕ :=
  Nat.gcd (Nat.nth (fun n => 1 ≤ n ∧ Squarefree n) (m - 1)) (Nat.nth IsCubefree (m - 1))

theorem main : ∀ k : ℕ, 1 ≤ k → Squarefree k → ∃ m : ℕ, 1 ≤ m ∧ a m = k := by
  sorry

end OMA.S_oeis_a070077
