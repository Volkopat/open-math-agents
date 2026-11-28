import OMAStatements.S_oeis_a000952
import Mathlib

namespace OMA.R_oeis_a000952_R1

open OMA.S_oeis_a000952

/-- Paley's symmetric conference matrices of prime-field order plus one. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → p % 4 = 1 →
    ∃ A : Matrix (Fin (p+1)) (Fin (p+1)) ℤ, A.IsSymm ∧ IsConferenceMatrix (p+1) A

def H2 : Prop := ∀ k : ℕ, k % 4 = 2 → ¬ (k-1).Prime →
    (∃ a b : ℕ, k-1 = a^2+b^2) → ∃ A : Matrix (Fin k) (Fin k) ℤ, IsConferenceMatrix k A

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000952.main := by
  intro h1 h2 k hk hs
  by_cases hp : (k-1).Prime
  · obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    obtain ⟨A,_,hA⟩ := h1 p (by simpa using hp) (by omega)
    exact ⟨A,hA⟩
  · exact h2 k hk hp hs

end OMA.R_oeis_a000952_R1
