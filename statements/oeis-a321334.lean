import Mathlib

/-!
# Squarefree complements in the upper half of an interval

Source: Frank M. Jackson, OEIS A321334 (2018), OEIS Foundation, CC BY-SA 4.0.
The displayed program requires a nonempty upper-half squarefree list and
starts at one. The condition n ≤ 2*s includes a midpoint for even n.
-/

namespace OMA.S_oeis_a321334

def upperSquarefree (n s : ℕ) : Prop := n ≤ 2*s ∧ s < n ∧ Squarefree s

def isTerm (n : ℕ) : Prop :=
  (∃ s, upperSquarefree n s) ∧ ∀ s, upperSquarefree n s → Squarefree (n-s)

theorem main : ∀ n : ℕ, isTerm n ↔ n ∈ ([2,3,4,5,6,7,8,12,13,16,36] : List ℕ) := by
  sorry

end OMA.S_oeis_a321334
