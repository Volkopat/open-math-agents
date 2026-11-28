import Mathlib

/-!
# Prime counts of squarefree integers

Source: https://oeis.org/A238646 (Zhi-Wei Sun)
Credit: @pyaf
-/

namespace OMA.S_oeis_a238646

/-- Number of squarefree positive integers at most m. -/
def squarefreeCount (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m).filter Squarefree).card

/-- A238646, indexed from 1. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun p => p.Prime ∧ (squarefreeCount (n - p)).Prime).card

theorem main :
    (∀ n : ℕ, 3 < n → 0 < a n) ∧
    (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ([4, 10, 12, 14, 16, 24, 36] : List ℕ))) := by
  sorry

end OMA.S_oeis_a238646
