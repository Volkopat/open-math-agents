import OMAStatements.S_mo_332147
import Mathlib

namespace OMA.R_mo_332147_R1

def H1 : Prop :=
  ∀ n : ℕ, 5 < n → IsSquare (2*n) → ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2*n ∧ jacobiSym (2*(n : ℤ)) p = 1

def H2 : Prop :=
  (∀ n : ℕ, 6 < n → ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2*n ∧ jacobiSym (-(n : ℤ)) p = -1) ∧
  (∀ n : ℕ, 5 < n → ¬IsSquare (2*n) → ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2*n ∧ jacobiSym (2*(n : ℤ)) p = 1)

theorem main : H1 → H2 → type_of% @OMA.S_mo_332147.main := by
  rintro hs ⟨hneg, hrest⟩
  refine ⟨hneg, fun n hn => ?_⟩
  by_cases h : IsSquare (2*n)
  · exact hs n hn h
  · exact hrest n hn h

end OMA.R_mo_332147_R1
