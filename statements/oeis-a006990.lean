import Mathlib

/-!
# OEIS A006990: n! minus the largest prime below it

Source: https://oeis.org/A006990
`a n` is the largest prime `≤ n!`. Conjecture: for `n ≥ 2`, `n! - a(n)` is `1` or a prime
(cf. A033933).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a006990

/-- The largest prime `≤ n!`. -/
noncomputable def a (n : ℕ) : ℕ := sSup {p | p.Prime ∧ p ≤ n.factorial}

theorem main :
    ∀ n : ℕ, 2 ≤ n → n.factorial - a n = 1 ∨ (n.factorial - a n).Prime := by
  sorry

end OMA.S_oeis_a006990
