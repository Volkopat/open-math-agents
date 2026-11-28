import FormalConjectures.Paper.StrongSensitivityConjecture

/-! Work in dimension 4*m, where the two accepting weights are integral.
The original proof is credited to @niclorusso. -/

namespace OMA.NisanSensitivity

open Finset StrongSensitivityConjecture

abbrev accepts (m w : ℕ) : Prop := w = 2 * m ∨ w = 2 * m + 1

lemma weight_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    #{j | StrongSensitivityConjecture.flip x {i} j} = if x i then #{j | x j} - 1 else #{j | x j} + 1 := by
  have h : ({j | StrongSensitivityConjecture.flip x {i} j} : Finset (Fin n)) =
      if x i then ({j | x j} : Finset (Fin n)).erase i else insert i ({j | x j} : Finset (Fin n)) := by
    split <;> ext j <;> by_cases hj : j = i <;> simp_all [StrongSensitivityConjecture.flip]
  rw [h]
  split <;> simp_all [card_erase_of_mem, card_insert_of_notMem]

lemma nisan_iff (m : ℕ) (x : Fin (4 * m) → Bool) :
    nisanExample (4 * m) x = true ↔ accepts m #{j | x j} := by
  have h (k : ℕ) : ((4 * m : ℕ) : ℚ) / 2 + k = (↑(2 * m + k) : ℚ) := by push_cast; ring
  have h0 : ((4 * m : ℕ) : ℚ) / 2 = (↑(2 * m) : ℚ) := by simpa using h 0
  have h1 : ((4 * m : ℕ) : ℚ) / 2 + 1 = (↑(2 * m + 1) : ℚ) := by simpa using h 1
  simp only [nisanExample, decide_eq_true_eq, mem_insert, mem_singleton]
  rw [h1, h0]
  simp only [Nat.cast_inj, accepts]

lemma sens_formula (m : ℕ) (x : Fin (4 * m) → Bool) :
    let w := #{j | x j}
    sensitivityAt (nisanExample (4 * m)) x =
      (if (accepts m (w - 1) ↔ accepts m w) then 0 else w) +
      (if (accepts m (w + 1) ↔ accepts m w) then 0 else 4 * m - w) := by
  dsimp only
  have key (i : Fin (4 * m)) :
      nisanExample (4 * m) (StrongSensitivityConjecture.flip x {i}) ≠ nisanExample (4 * m) x ↔
      (x i = true ∧ ¬(accepts m (#{j | x j} - 1) ↔ accepts m #{j | x j})) ∨
      (x i = false ∧ ¬(accepts m (#{j | x j} + 1) ↔ accepts m #{j | x j})) := by
    rw [Ne, Bool.eq_iff_iff, nisan_iff, nisan_iff, weight_flip]
    cases x i <;> simp
  have hsplit := card_filter_add_card_filter_not (s := univ) fun j => x j = true
  simp only [card_univ, Fintype.card_fin, Bool.not_eq_true] at hsplit
  unfold sensitivityAt
  simp_rw [key]
  by_cases hA : (accepts m (#{j | x j} - 1) ↔ accepts m #{j | x j}) <;>
    by_cases hC : (accepts m (#{j | x j} + 1) ↔ accepts m #{j | x j}) <;>
    simp [hA, hC] <;> omega

end OMA.NisanSensitivity

open Finset StrongSensitivityConjecture OMA.NisanSensitivity in
theorem OMA.solution : type_of% @StrongSensitivityConjecture.nisanExample_sensitivity := by
  intro n hn hp
  obtain ⟨m, rfl⟩ := hn
  have hdiv : 4 * m / 2 + 2 = 2 * m + 2 := by omega
  rw [hdiv]
  apply le_antisymm
  · apply Finset.sup_le
    intro x _
    rw [sens_formula]
    have hw : #{j | x j} ≤ 4 * m := by
      simpa using card_filter_le (univ : Finset (Fin (4 * m))) (fun j => x j = true)
    generalize #{j | x j} = w at hw ⊢
    by_cases hA : (accepts m (w - 1) ↔ accepts m w) <;>
      by_cases hC : (accepts m (w + 1) ↔ accepts m w) <;>
      simp only [hA, hC, if_true, if_false] <;>
      simp only [accepts] at hA hC <;> omega
  · obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (4 * m))))
      (n := 2 * m + 2) (by simp; omega)
    let x (i : Fin (4 * m)) := decide (i ∈ S)
    have hx : #{j | x j} = 2 * m + 2 := by simp [x, hS]
    calc 2 * m + 2 = sensitivityAt (nisanExample (4 * m)) x := by
          rw [sens_formula]
          rw [hx, if_neg (by unfold accepts; omega), if_pos (by unfold accepts; omega), add_zero]
      _ ≤ _ := Finset.le_sup (mem_univ x)
