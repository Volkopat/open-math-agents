import OMAStatements.S_mo_511338

/-!
At k = 1 the lower bound allows weights strictly between zero and one.
For the family consisting of the empty set and a two-element universe,
the proposed inequality at either element reduces to t ≤ t².
-/

namespace WeightedTwoPointFamily

open OMA.S_mo_511338

private def family : Finset (Finset (Fin 2)) := {∅, Finset.univ}

private theorem closed : KUnionClosed 1 family := by
  unfold KUnionClosed family
  decide +kernel

private theorem covers : family.sup id = Finset.univ := by decide +kernel

private theorem fails (i : Fin 2) (t : ℝ) (ht : 0 < t) (h₁ : t < 1) :
    ¬ t * ∑ S ∈ family.filter (fun S => i ∉ S), ∏ _j ∈ S, t ≤
      ∑ S ∈ family.filter (fun S => i ∈ S), ∏ _j ∈ S, t := by
  have absent : family.filter (fun S => i ∉ S) = {∅} := by
    fin_cases i <;> decide +kernel
  have present : family.filter (fun S => i ∈ S) = {Finset.univ} := by
    fin_cases i <;> decide +kernel
  rw [absent, present]
  simpa [sq] using not_le.mpr (show t * t < t by nlinarith [mul_pos ht (sub_pos.mpr h₁)])

end WeightedTwoPointFamily

open OMA.S_mo_511338 WeightedTwoPointFamily

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_511338.main) := by
  intro h
  obtain ⟨i, hi⟩ := h 2 1 family (by decide) (by decide) closed covers
    (fun _ => (1 / 2 : ℝ)) (by intro j; norm_num)
  exact fails i (1 / 2) (by norm_num) (by norm_num) hi
