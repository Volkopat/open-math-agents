import Mathlib

/-!
# Zhi-Wei Sun's Conjecture 1(i) in OEIS A362861

Both sentences of Conjecture 1(i), proposed May 5, 2023.
OEIS Foundation, CC BY-SA 4.0. https://oeis.org/A362861
-/

namespace OMA.S_oeis_a362861

def canRepresent (k m n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ v ∈ s, ∃ a b : ℕ, v = k^a + m^b) ∧ ∑ v ∈ s, v = n

theorem main :
    (∀ n : ℕ, 0 < n → (¬ canRepresent 5 5 (2*n) ↔
      n ∈ ([2,7,10,11,12,27,35,50,51,52,55,60,135,255] : List ℕ))) ∧
    (∀ n : ℕ, 0 < n → canRepresent 3 3 (2*n)) := by
  sorry

end OMA.S_oeis_a362861
