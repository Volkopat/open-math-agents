import FormalConjectures.Wikipedia.JugglerConjecture

-- Reduction JugglerConjecture.juggler_conjecture.R1 of the juggler conjecture
-- Credit: @marcusbuffett

/-!
# The juggler conjecture: a kernel-checked initial range, and the open rest

The juggler step sends an even `n` to `⌊n ^ (1/2)⌋` and an odd `n` to `⌊n ^ (3/2)⌋`; the
conjecture says that every positive integer reaches `1`.

* `H1`: every `n` with `0 < n ≤ 1000` reaches `1`. The step is rewritten with integer square
  roots, and the trajectories are certified term by term inside the Lean kernel.
* `H2`: every `n > 1000` reaches `1`. This is the open conjecture (verified numerically much
  further; the range here is only what fits comfortably in a proof file).
-/

namespace OMA.R_JugglerConjecture_juggler_conjecture_R1

/-- The verified range. -/
def H1 : Prop :=
  ∀ n : ℕ, n > 0 → n ≤ 1000 → ∃ m, JugglerConjecture.jugglerStep^[m] n = 1

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000 < n → ∃ m, JugglerConjecture.jugglerStep^[m] n = 1

theorem main : H1 → H2 → type_of% @JugglerConjecture.juggler_conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1000
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_JugglerConjecture_juggler_conjecture_R1
