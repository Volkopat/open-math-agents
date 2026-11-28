import Mathlib

/-!
# OEIS A076259: large gaps between squarefree numbers

Source: https://oeis.org/A076259
`a n = s(n+1) - s(n)`, where `s(n)` is the `n`-th squarefree number. Conjecture (Ordowski,
2015): `limsup a(n) / log s(n) = 1/2` (equivalently `limsup a(n)/log n = 1/2`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a076259

open Filter Real

/-- The `n`-th squarefree number, indexed from `1`. -/
noncomputable def s (n : ℕ) : ℕ := Nat.nth (fun m => 1 ≤ m ∧ Squarefree m) (n - 1)

theorem main :
    limsup (fun n : ℕ => ((s (n + 1) : ℝ) - s n) / log (s n)) atTop = 1 / 2 := by
  sorry

end OMA.S_oeis_a076259
