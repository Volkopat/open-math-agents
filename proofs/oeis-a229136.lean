import OMAStatements.S_oeis_a229136
import Mathlib
open OMA.S_oeis_a229136

theorem a229_count_eq_sum (n : ℕ) (r : ZMod 4) :
    count n r = ∑ y : Fin n → Fin 4, if ∑ i, digitSquare (y i) = r then 1 else 0 := by
  unfold count solutions
  rw [Fintype.card_subtype, Finset.card_filter]

theorem a229_count_zero (r : ZMod 4) : count 0 r = if r = 0 then 1 else 0 := by
  rw [a229_count_eq_sum]
  simp [eq_comm]

theorem a229_count_succ (n : ℕ) (r : ZMod 4) :
    count (n + 1) r = 2 * count n r + 2 * count n (r - 1) := by
  simp only [a229_count_eq_sum]
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Fin 4).sum_comp]
  simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four]
  simp only [show digitSquare 0 = 0 by decide, show digitSquare 1 = 1 by decide,
    show digitSquare 2 = 0 by decide, show digitSquare 3 = 1 by decide, zero_add]
  have key : ∀ y : Fin n → Fin 4, ((1 : ZMod 4) + ∑ i, digitSquare (y i) = r) ↔
      (∑ i, digitSquare (y i) = r - 1) := by
    intro y; rw [eq_sub_iff_add_eq, add_comm]
  simp only [key]
  ring

theorem a229_rec4 (n : ℕ) (r : ZMod 4) :
    (count (n + 4) r : ℤ) = 8 * count (n + 3) r - 24 * count (n + 2) r + 32 * count (n + 1) r := by
  simp only [a229_count_succ]
  push_cast
  have e : ∀ s : ZMod 4, s - 1 - 1 - 1 - 1 = s := by decide
  simp only [e]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a229136.main := by
  have P : ∀ n, (a (n + 1) : ℤ) = b (n + 1) * 2 ^ n ∧ (a (n + 2) : ℤ) = b (n + 2) * 2 ^ (n + 1)
      ∧ (a (n + 3) : ℤ) = b (n + 3) * 2 ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      simp only [a, a229_count_succ, a229_count_zero]
      refine ⟨?_, ?_, ?_⟩ <;> simp [b] <;> decide
    | succ k ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      refine ⟨i2, i3, ?_⟩
      have h4 := a229_rec4 k 1
      unfold a at i1 i2 i3 ⊢
      rw [show k + 1 + 3 = k + 4 by ring, h4, show k + 1 + 2 = k + 3 by ring, i1, i2, i3,
        show k + 4 = k + 0 + 4 by ring, b]
      ring
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using (P m).1
