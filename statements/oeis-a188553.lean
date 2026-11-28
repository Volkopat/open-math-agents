import Mathlib

/-!
# Fiol's binary-array and word enumeration

The rows run from top to bottom and columns from left to right. The vertical
condition says that each column is weakly decreasing. This is equivalent to
forbidding a zero immediately above a one. The other three inequalities
forbid a zero followed by a one in the horizontal and two downward diagonal
directions. A word records the number of ones in each column.

Source: https://oeis.org/A188553 (OEIS Foundation, CC BY-SA 4.0)
Credit: @connoranderson
-/

namespace OMA.S_oeis_a188553

def Avoids {n k : ℕ} (A : Fin n → Fin k → Fin 2) : Prop :=
  (∀ j, Antitone (fun i => A i j)) ∧
  ∀ j j' : Fin k, j.val+1=j'.val →
    (∀ i, A i j' ≤ A i j) ∧
    ∀ i i' : Fin n, i.val+1=i'.val →
      A i' j' ≤ A i j ∧ A i' j ≤ A i j'

def Steps {n k : ℕ} (w : Fin k → Fin (n+1)) : Prop :=
  ∀ j j' : Fin k, j.val+1=j'.val →
    (w j').val=(w j).val ∨ (w j').val+1=(w j).val

theorem main : ∀ n k : ℕ, 0 < n → 0 < k →
    Nat.card { A : Fin n → Fin k → Fin 2 // Avoids A } =
    Nat.card { w : Fin k → Fin (n+1) // Steps w } := by
  sorry

end OMA.S_oeis_a188553
