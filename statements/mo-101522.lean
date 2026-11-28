import Mathlib

/-!
# MathOverflow 101522

Source: https://mathoverflow.net/questions/101522
-/

namespace OMA.S_mo_101522

open Finset

def bitValue : Bool → ℝ
  | true => 1
  | false => 0

def rowValue {m n : ℕ} (U : Fin m → Fin n → ℝ) (i : Fin m) (y : Fin n → Bool) : ℝ :=
  ∑ j, U i j * bitValue (y j)

def assignmentValue {m n : ℕ} (U : Fin m → Fin n → ℝ) (X : Fin m → Fin n → Bool) : ℝ :=
  ∑ i, rowValue U i (X i)

def Feasible {m n : ℕ} (f : Fin m → Fin n → ℝ) (c : Fin n → ℝ)
    (X : Fin m → Fin n → Bool) : Prop :=
  ∀ j, ∑ i, f i j * bitValue (X i j) ≤ c j

def GlobalMaximum {m n : ℕ} (U f : Fin m → Fin n → ℝ) (c : Fin n → ℝ)
    (X : Fin m → Fin n → Bool) : Prop :=
  Feasible f c X ∧ ∀ Y, Feasible f c Y → assignmentValue U Y ≤ assignmentValue U X

def WithinRemaining {m n : ℕ} (f : Fin m → Fin n → ℝ) (c : Fin n → ℝ)
    (π : Equiv.Perm (Fin m)) (X : Fin m → Fin n → Bool) (t : Fin m) (y : Fin n → Bool) :
    Prop :=
  ∀ j, (∑ s ∈ univ.filter (· < t), f (π s) j * bitValue (X (π s) j)) +
    f (π t) j * bitValue (y j) ≤ c j

def RowwiseMaximum {m n : ℕ} (U f : Fin m → Fin n → ℝ) (c : Fin n → ℝ)
    (π : Equiv.Perm (Fin m)) (X : Fin m → Fin n → Bool) : Prop :=
  ∀ t, WithinRemaining f c π X t (X (π t)) ∧
    ∀ y, WithinRemaining f c π X t y → rowValue U (π t) y ≤ rowValue U (π t) (X (π t))

theorem main : ∀ (m n : ℕ) (U f : Fin m → Fin n → ℝ) (c : Fin n → ℝ),
    (∃ X, Feasible f c X) → ∃ (π : Equiv.Perm (Fin m)) (X : Fin m → Fin n → Bool),
      GlobalMaximum U f c X ∧ RowwiseMaximum U f c π X := by
  sorry

end OMA.S_mo_101522
