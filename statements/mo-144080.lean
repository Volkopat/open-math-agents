import Mathlib

/-!
# Is `liminf |n sin n| = 0` over the integers?

Source: https://mathoverflow.net/questions/144080/is-varliminf-n-rightarrow-infty-n-sin-n-0-correct-where-n-is-an
Credit: @shc261392

Question. Is it true that `liminf_{n → +∞} |n sin n| = 0`, where `n` runs over the integers?
(The liminf is finite by Dirichlet's approximation theorem.)

Reading used here (the affirmative answer): for every `ε > 0` there are arbitrarily large
natural numbers `n` with `|n sin n| < ε`.
-/

namespace OMA.S_mo_144080

theorem main :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N < n ∧ |(n : ℝ) * Real.sin n| < ε := by
  sorry

end OMA.S_mo_144080
