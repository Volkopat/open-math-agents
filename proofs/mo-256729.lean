import OMAStatements.S_mo_256729

open scoped BigOperators

namespace OMA.LinearSearch

private theorem bounded_solution {m n : ℕ} (A : Fin m → Fin n → ℕ) (b : Fin m → ℕ) :
    (∃ x : Fin n → ℕ, ∀ i, ∑ j, A i j * x j = b i) ↔
      ∃ x : Fin n → Fin ((∑ i, b i) + 1), ∀ i, ∑ j, A i j * (x j).val = b i := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    let y : Fin n → ℕ := fun j => if ∃ i, 0 < A i j then x j else 0
    have bound (j : Fin n) : y j ≤ ∑ i, b i := by
      by_cases h : ∃ i, 0 < A i j
      · rw [show y j = x j by simp [y, h]]
        obtain ⟨i, hi⟩ := h
        calc
          x j = 1 * x j := (one_mul _).symm
          _ ≤ A i j * x j := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)
          _ ≤ ∑ k, A i k * x k :=
            Finset.single_le_sum (fun k _ => Nat.zero_le (A i k * x k)) (Finset.mem_univ j)
          _ = b i := hx i
          _ ≤ ∑ k, b k :=
            Finset.single_le_sum (fun k _ => Nat.zero_le (b k)) (Finset.mem_univ i)
      · simp [y, h]
    refine ⟨fun j => ⟨y j, Nat.lt_succ_of_le (bound j)⟩, ?_⟩
    intro i
    change ∑ j, A i j * y j = b i
    rw [← hx i]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : ∃ i, 0 < A i j
    · simp [y, h]
    · have hz : A i j = 0 := Nat.eq_zero_of_not_pos (fun hi => h ⟨i, hi⟩)
      simp [hz]
  · rintro ⟨x, hx⟩
    exact ⟨fun j => (x j).val, hx⟩

end OMA.LinearSearch

theorem OMA.solution : type_of% @OMA.S_mo_256729.main := by
  intro m n A b
  have h := OMA.LinearSearch.bounded_solution A b
  refine ⟨h, ?_⟩
  rw [OMA.S_mo_256729.hasSolution, decide_eq_true_eq]
  exact h.symm