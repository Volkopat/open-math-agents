import OMAStatements.S_oeis_a026008
import Mathlib.Tactic

open OMA.S_oeis_a026008

namespace CatalanDiagonal

lemma even_index (k : ℕ) : a (2*k) = evenTerm k := by
  simp [a]

lemma odd_index (k : ℕ) : a (2*k+1) = oddTerm k := by
  rw [a, if_neg (show ¬ (2*k+1)%2 = 0 by omega),
    show (2*k+1)/2 = k by omega]

end CatalanDiagonal

open CatalanDiagonal

theorem OMA.solution : type_of% @OMA.S_oeis_a026008.main := by
  intro t
  obtain ⟨k, rfl | rfl⟩ : ∃ k, t = 2*k ∨ t = 2*k+1 := ⟨t/2, by omega⟩
  · rw [show 2*k+4 = 2*(k+2) by omega, show 2*k+3 = 2*(k+1)+1 by omega,
      show 2*k+2 = 2*(k+1) by omega, even_index, odd_index, even_index, odd_index, even_index]
    simp [evenTerm, oddTerm, mul_add, Nat.factorial_succ]
    field_simp
    ring
  · rw [show 2*k+1+4 = 2*(k+2)+1 by omega, show 2*k+1+3 = 2*(k+2) by omega,
      show 2*k+1+2 = 2*(k+1)+1 by omega, show 2*k+1+1 = 2*(k+1) by omega,
      odd_index, even_index, odd_index, even_index, odd_index]
    simp [evenTerm, oddTerm, mul_add, Nat.factorial_succ]
    field_simp
    ring
