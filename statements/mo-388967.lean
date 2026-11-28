import Mathlib

/-!
# Minimum span dimension of a family of rank-one matrices

Source: https://mathoverflow.net/questions/388967
Credit: @Takkun-kohinata
Question by Kevin on MathOverflow (CC BY-SA).
The index set is the natural numbers, and the complex dimension n is positive.
-/

namespace OMA.S_mo_388967

abbrev Sq (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def Admissible (n : ℕ) (A : ℕ → Sq n) : Prop :=
  (∀ i, (A i).rank = 1) ∧
    ∀ s : Finset ℕ, s.card = n → IsUnit (∑ i ∈ s, A i).det

theorem main : ∀ n : ℕ, 0 < n →
    IsLeast {d : ℕ | ∃ A : ℕ → Sq n, Admissible n A ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = d} (2 * n - 1) := by
  sorry

end OMA.S_mo_388967
