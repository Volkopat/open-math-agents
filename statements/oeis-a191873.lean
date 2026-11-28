import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Defs

/-!
# Zero-diagonal rectangle-free boards

A board is the set of positions occupied by ones. A191873 maximizes the weight
among rectangle-free boards with empty diagonal. A072567 maximizes over all
rectangle-free boards. A001197 is the least feasible weight at which every
board contains a rectangle.

Source: https://oeis.org/A191873
Related definitions: https://oeis.org/A072567 and https://oeis.org/A001197
Credit: @LDJAI
-/

namespace OMA.S_oeis_a191873

abbrev Board (n : ℕ) := Finset (Fin n × Fin n)

def rectangleFree {n : ℕ} (A : Board n) : Prop :=
  ∀ i k j l, i ≠ k → j ≠ l →
    (i,j) ∈ A → (i,l) ∈ A → (k,j) ∈ A → (k,l) ∈ A → False

def weights (n : ℕ) : Set ℕ :=
  {d | ∃ A : Board n, rectangleFree A ∧ A.card = d}

def diagonalWeights (n : ℕ) : Set ℕ :=
  {d | ∃ A : Board n, rectangleFree A ∧ (∀ i, (i,i) ∉ A) ∧ A.card = d}

def forcingWeights (n : ℕ) : Set ℕ :=
  {k | k ≤ n*n ∧ ∀ A : Board n, A.card = k → ¬rectangleFree A}

theorem main : ∀ n : ℕ, 3 ≤ n → ∃ d z k : ℕ,
    IsGreatest (diagonalWeights n) d ∧ IsGreatest (weights n) z ∧
    IsLeast (forcingWeights n) k ∧ d = z ∧ z = k-1 := by
  sorry

end OMA.S_oeis_a191873
