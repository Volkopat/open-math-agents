import Mathlib

/-! Source: https://math.stackexchange.com/questions/1022617 -/

namespace OMA.S_mse_1022617

/-- Retain the original index order after a difference step. Absent values do not contribute to the row. -/
noncomputable def nextRow (a : ℕ → Option ℕ) (i : ℕ) : Option ℕ := by
  classical
  exact match a i with
  | none => none
  | some v =>
    if h : ∃ j : ℕ, i < j ∧ ∃ w : ℕ, a j = some w ∧ v ≤ w then
      (a (Nat.find h)).map (fun w => w - v)
    else none

/-- Row zero is the sequence of primes. -/
noncomputable def row (r : ℕ) : ℕ → Option ℕ :=
  (nextRow^[r]) (fun i => some (Nat.nth Nat.Prime i))

theorem main :
    ∀ r : ℕ, 0 < r → ∃ i : ℕ, row r i = some 1 ∧ ∀ j < i, row r j = none := by
  sorry

end OMA.S_mse_1022617
