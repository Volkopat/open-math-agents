import Mathlib

/-!
# A 6-avoidable but not 5-avoidable word?

Source: https://mathoverflow.net/questions/93997
A pattern (word over variables) `u` is `k`-avoidable if there is an infinite word over `k`
letters containing no factor of the form `h(u)` with `h` a non-erasing substitution of
nonempty words for the variables. Is there a word that is `6`-avoidable but not
`5`-avoidable? `main` states the affirmative answer.

Conventions. Patterns are lists of natural numbers (variables); infinite words over `k`
letters are maps `ℕ → Fin k`. A finite word `v` is a factor of `w` if `v = w i, …, w (i+|v|-1)`
for some `i`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_93997

/-- `v` occurs as a factor of the infinite word `w`. -/
def IsFactor {k : ℕ} (v : List (Fin k)) (w : ℕ → Fin k) : Prop :=
  ∃ i : ℕ, ∀ j : Fin v.length, w (i + j) = v.get j

/-- The pattern `u` is avoidable over `k` letters. -/
def Avoidable (u : List ℕ) (k : ℕ) : Prop :=
  ∃ w : ℕ → Fin k, ∀ h : ℕ → List (Fin k), (∀ x ∈ u, h x ≠ []) → ¬ IsFactor (u.flatMap h) w

theorem main : ∃ u : List ℕ, Avoidable u 6 ∧ ¬ Avoidable u 5 := by
  sorry

end OMA.S_mo_93997
