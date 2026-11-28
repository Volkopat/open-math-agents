import OMAStatements.S_wpc_prouhet_tarry_escott
import Mathlib

/-!
Reduction wpc-prouhet-tarry-escott.R1: ideal Prouhet–Tarry–Escott solutions, split by degree.

H1 is the classical range: ideal solutions are known for every degree `k ≤ 9` and for `k = 11`
(sizes `n = k + 1 ≤ 10` and `n = 12`; Prouhet, Tarry, Escott, Letac, Smyth, Kuosa, Meyrignac and
Chen). These are known cases, not progress on the problem.
H2 is the open remainder: degree `10` and every degree `k ≥ 12`.
-/

namespace OMA.R_wpc_prouhet_tarry_escott_R1

open OMA.S_wpc_prouhet_tarry_escott (IsIdealSolution)

/-- Ideal solutions exist in every degree `k ≤ 9` and in degree `11`. -/
def H1 : Prop :=
  ∀ k : ℕ, (k ≤ 9 ∨ k = 11) → ∃ A B : Multiset ℤ, IsIdealSolution k A B

/-- The open remainder: degree `10` and every degree `k ≥ 12`. -/
def H2 : Prop :=
  ∀ k : ℕ, (k = 10 ∨ 12 ≤ k) → ∃ A B : Multiset ℤ, IsIdealSolution k A B

theorem main : H1 → H2 → type_of% @OMA.S_wpc_prouhet_tarry_escott.main := by
  intro h1 h2 k
  by_cases h : k ≤ 9 ∨ k = 11
  · exact h1 k h
  · exact h2 k (by omega)

end OMA.R_wpc_prouhet_tarry_escott_R1
