import Mathlib

/-!
# OEIS A122536: binary sequences with no initial repeats

Source: https://oeis.org/A122536
`a n` is the number of binary sequences of length `n` with no initial repeat, i.e. no prefix
of the form `w w` with `w` nonempty. Conjecture (Chaffin, Linderman, Sloane, Wilks, 2012):
`a n ~ C 2^n` with `C = 0.27004339525…`. `main` states that `a n / 2^n` converges to a
positive constant (the numerical value is not part of the statement).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a122536

open Filter Topology

/-- Binary words of length `n` without a prefix `w w`, `w ≠ []`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {s : List Bool | s.length = n ∧ ¬ ∃ w : List Bool, w ≠ [] ∧ w ++ w <+: s}

theorem main : ∃ C : ℝ, 0 < C ∧ Tendsto (fun n : ℕ => (a n : ℝ) / 2 ^ n) atTop (𝓝 C) := by
  sorry

end OMA.S_oeis_a122536
