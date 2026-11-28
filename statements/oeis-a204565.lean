import Mathlib

/-!
# OEIS A204565

Number of `(n + 1) × 2` `0..3` arrays with every `2 × 2` subblock having equal diagonal
elements or equal antidiagonal elements, and new values `0..3` introduced in row major order.

Conjectured by Colin Barker (Jun 07 2018):
* `3 * a(n) = 1 + 3 * 3 ^ n + 2 * 7 ^ n` (i.e. `a(n) = 1/3 + 3^n + (2 * 7^n) / 3`) for all `n ≥ 1`.
-/

namespace OMA.S_oeis_a204565

/-- An `(n + 1) × 2` array over `Fin 4` is valid if every `2 × 2` subblock has equal diagonal
or equal antidiagonal elements and new values `0..3` are introduced in row-major order. -/
def isValid (n : ℕ) (A : Fin (n + 1) → Fin 2 → Fin 4) : Prop :=
  (∀ i : Fin n, A i.castSucc 0 = A i.succ 1 ∨ A i.castSucc 1 = A i.succ 0) ∧
  (∀ (i : Fin (n + 1)) (j : Fin 2) (v : Fin 4), v < A i j →
    ∃ (i' : Fin (n + 1)) (j' : Fin 2), 2 * i'.1 + j'.1 < 2 * i.1 + j.1 ∧ A i' j' = v)

/-- `a(n)` is the number of valid `(n + 1) × 2` arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin (n + 1) → Fin 2 → Fin 4 // isValid n A}

theorem main :
    ∀ n : ℕ, 1 ≤ n → 3 * a n = 1 + 3 * 3 ^ n + 2 * 7 ^ n := by
  sorry

end OMA.S_oeis_a204565
