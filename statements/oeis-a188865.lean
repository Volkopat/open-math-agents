import Mathlib

/-!
# OEIS A188865

Number of `n × 8` binary arrays without the pattern `0 1` diagonally, vertically, or antidiagonally.

Conjectured by Colin Barker (Feb 28 2018):
* `a(n) + a(n - 2) = 2 * a(n - 1)` (i.e. `a(n) = 2 * a(n - 1) - a(n - 2)`) for all `n > 7`.
-/

namespace OMA.S_oeis_a188865

/-- An `n × 8` binary array `A : Fin n → Fin 8 → Fin 2` avoids the pattern `0 1` vertically,
diagonally, and antidiagonally if whenever `A i j = 0`, all neighbors `(i + 1, j')` with
`|j' - j| ≤ 1` also equal `0`. -/
def isValid (n : ℕ) (A : Fin n → Fin 8 → Fin 2) : Prop :=
  ∀ (i : Fin n) (hi : i.1 + 1 < n) (j j' : Fin 8),
    j'.1 ≤ j.1 + 1 → j.1 ≤ j'.1 + 1 → A i j = 0 → A ⟨i.1 + 1, hi⟩ j' = 0

/-- `a(n)` is the number of valid `n × 8` binary arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin n → Fin 8 → Fin 2 // isValid n A}

theorem main :
    ∀ n : ℕ, 7 < n → a n + a (n - 2) = 2 * a (n - 1) := by
  sorry

end OMA.S_oeis_a188865
