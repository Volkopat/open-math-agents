import OMAStatements.S_mo_101522

namespace OMA
open Finset S_mo_101522

private noncomputable def value (i j : Fin 3) : ℝ := if i = j then 3 else 2
private noncomputable def cost (i j : Fin 3) : ℝ := if i = j then 2 else 1
private def candidate (i j : Fin 3) : Bool := decide (i ≠ j)

private theorem finThree : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

private theorem two_ne_zero : (2 : Fin 3) ≠ 0 := by decide
private theorem zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
private theorem two_ne_one : (2 : Fin 3) ≠ 1 := by decide
private theorem one_ne_two : (1 : Fin 3) ≠ 2 := by decide

private theorem candidateFeasible : Feasible cost (fun _ => 2) candidate := by
  intro j
  rcases finThree j with rfl | rfl | rfl <;>
    norm_num [Fin.sum_univ_three, cost, candidate, bitValue,
      two_ne_zero, zero_ne_two, two_ne_one, one_ne_two]

private theorem candidateValue : assignmentValue value candidate = 12 := by
  norm_num [assignmentValue, rowValue, Fin.sum_univ_three, value, candidate,
    bitValue, two_ne_zero, zero_ne_two, two_ne_one, one_ne_two]

private theorem columnBounds (j : Fin 3) (y : Fin 3 → Bool)
    (h : ∑ i, cost i j * bitValue (y i) ≤ 2) :
    (∑ i, value i j * bitValue (y i) ≤ 4) ∧
      (y j = true → ∑ i, value i j * bitValue (y i) ≤ 3) := by
  rcases finThree j with rfl | rfl | rfl <;> cases h₀ : y 0 <;>
    cases h₁ : y 1 <;> cases h₂ : y 2 <;>
    norm_num [Fin.sum_univ_three, cost, bitValue,
      two_ne_zero, zero_ne_two, two_ne_one, one_ne_two, h₀, h₁, h₂] at h <;>
    norm_num [Fin.sum_univ_three, value, bitValue,
      two_ne_zero, zero_ne_two, two_ne_one, one_ne_two, h₀, h₁, h₂]

private theorem firstRowValue (i : Fin 3) (y : Fin 3 → Bool)
    (h : rowValue value i (fun _ => true) ≤ rowValue value i y) : y i = true := by
  rcases finThree i with rfl | rfl | rfl <;> cases h₀ : y 0 <;>
    cases h₁ : y 1 <;> cases h₂ : y 2 <;>
    norm_num [rowValue, Fin.sum_univ_three, value, bitValue,
      two_ne_zero, zero_ne_two, two_ne_one, one_ne_two, h₀, h₁, h₂] at *

end OMA

open Finset OMA OMA.S_mo_101522 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_101522.main) := by
  intro h
  obtain ⟨π, X, hG, hR⟩ := h 3 3 value cost (fun _ => 2) ⟨candidate, candidateFeasible⟩
  have hfit : WithinRemaining cost (fun _ => 2) π X 0 (fun _ => true) := by
    have hzero : ∀ i : Fin 3, ¬ i < 0 := fun i => by omega
    intro j
    simp only [hzero, filter_false, sum_empty, zero_add, bitValue, mul_one, cost]
    split <;> norm_num
  have hfirst : X (π 0) (π 0) = true := firstRowValue _ _ ((hR 0).2 _ hfit)
  have hge : 12 ≤ assignmentValue value X := candidateValue ▸ hG.2 candidate candidateFeasible
  have hcol (j : Fin 3) :=
    columnBounds j (fun i => X i j) (hG.1 j)
  have hlt : (∑ j : Fin 3, ∑ i : Fin 3, value i j * bitValue (X i j)) < ∑ _ : Fin 3, (4 : ℝ) :=
    sum_lt_sum (fun j _ => (hcol j).1)
      ⟨π 0, mem_univ _, lt_of_le_of_lt ((hcol (π 0)).2 hfirst) (by norm_num)⟩
  rw [sum_comm] at hlt
  have hsum : (∑ _ : Fin 3, (4 : ℝ)) = 12 := by norm_num
  rw [hsum] at hlt
  apply not_lt_of_ge hge
  exact hlt

