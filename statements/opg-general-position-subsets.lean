import Mathlib

/-!
# General position subsets

Source: https://www.openproblemgarden.org/op/general_position_subsets
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Wood): what is the least integer `f(n)` such that every set of at least `f(n)` points
in the plane contains `n` collinear points or `n` points in general position (no three
collinear)? It is known that `f(n) = Ω(n²)` (grid) and `f(n) = O(n² log n)` (Payne–Wood).

Conventions:
* The source asks for `f(n)`; it states the conjectured answer "it is reasonable to think that
  the grid is the extremal example, and `f(n) ≤ O(n²)`". `main` states this conjecture: there is
  a constant `C` such that every finite set of at least `C n²` points in the plane contains `n`
  collinear points or `n` points in general position.
* Points are in `ℝ²`; collinearity is Mathlib's `Collinear`.
-/

namespace OMA.S_opg_general_position_subsets

/-- The plane. -/
abbrev P := EuclideanSpace ℝ (Fin 2)

/-- No three points of `S` are collinear. -/
def GeneralPosition (S : Finset P) : Prop :=
  ∀ T ⊆ S, T.card = 3 → ¬ Collinear ℝ (T : Set P)

theorem main :
    ∃ C : ℝ, ∀ (n : ℕ) (A : Finset P), C * (n : ℝ) ^ 2 ≤ A.card →
      (∃ T ⊆ A, T.card = n ∧ Collinear ℝ (T : Set P)) ∨
        (∃ T ⊆ A, T.card = n ∧ GeneralPosition T) := by
  sorry

end OMA.S_opg_general_position_subsets
