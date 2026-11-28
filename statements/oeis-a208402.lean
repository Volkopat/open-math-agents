import Mathlib

/-!
# OEIS A208402

Number of `n × 2` `0..3` arrays with new values `0..3` introduced in row major order
and no element equal to more than two of its immediate leftward or upward or
right-upward antidiagonal neighbors.

Conjectured by Colin Barker (Jul 02 2018):
* `a(n) = (8 + 3 * 2 ^ (1 + 2 * n) + 16 ^ n) / 24` for all `n ≥ 1`.
-/

namespace OMA.S_oeis_a208402

/-- Number of immediate leftward, upward, or right-upward antidiagonal neighbors of `(i, j)`
in an `n × 2` array `A` whose value equals `A i j`. -/
def eqNeighborCount {n : ℕ} (A : Fin n → Fin 2 → Fin 4) (i : Fin n) (j : Fin 2) : ℕ :=
  (if h : 0 < j.1 then if A i ⟨j.1 - 1, by omega⟩ = A i j then 1 else 0 else 0) +
  (if h : 0 < i.1 then if A ⟨i.1 - 1, by omega⟩ j = A i j then 1 else 0 else 0) +
  (if h : 0 < i.1 ∧ j.1 + 1 < 2 then if A ⟨i.1 - 1, by omega⟩ ⟨j.1 + 1, h.2⟩ = A i j then 1 else 0 else 0)

/-- An `n × 2` array over `Fin 4` is valid if new values `0..3` are introduced in row-major order
and no element equals more than two of its immediate leftward, upward, or right-upward neighbors. -/
def isValid (n : ℕ) (A : Fin n → Fin 2 → Fin 4) : Prop :=
  (∀ (i : Fin n) (j : Fin 2) (v : Fin 4), v < A i j →
    ∃ (i' : Fin n) (j' : Fin 2), 2 * i'.1 + j'.1 < 2 * i.1 + j.1 ∧ A i' j' = v) ∧
  (∀ (i : Fin n) (j : Fin 2), eqNeighborCount A i j ≤ 2)

/-- `a(n)` is the number of valid `n × 2` arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin n → Fin 2 → Fin 4 // isValid n A}

theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = (8 + 3 * 2 ^ (1 + 2 * n) + 16 ^ n) / 24 := by
  sorry

end OMA.S_oeis_a208402
