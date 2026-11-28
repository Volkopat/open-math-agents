import OMAStatements.S_oeis_a159999
import Mathlib

namespace A159999Aux

open OMA.S_oeis_a159999 in
lemma traj_add (n i k : ℕ) : trajectory n (i + k) = trajectory (trajectory n i) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show collatzStep (trajectory n (i + k)) = collatzStep (trajectory (trajectory n i) k)
    rw [ih]

open OMA.S_oeis_a159999 in
lemma stopping_spec (n : ℕ) (h : ∃ k : ℕ, trajectory n k = 1) :
    trajectory n (stopping n) = 1 ∧ ∀ m < stopping n, trajectory n m ≠ 1 := by
  classical
  unfold stopping
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun m hm => Nat.find_min h hm⟩

end A159999Aux

open OMA.S_oeis_a159999 in
theorem OMA.solution : type_of% @OMA.S_oeis_a159999.main := by
  intro hC n hn
  obtain ⟨hs, hmin⟩ := A159999Aux.stopping_spec n (hC n hn)
  have key : ∀ i j : ℕ, i < j → j ≤ stopping n → trajectory n i ≠ trajectory n j := by
    intro i j hij hj heq
    have h1 : trajectory n (i + (stopping n - j)) = 1 := by
      rw [A159999Aux.traj_add, heq, ← A159999Aux.traj_add,
        show j + (stopping n - j) = stopping n by omega]
      exact hs
    exact hmin _ (by omega) h1
  refine ⟨key, ?_⟩
  have h0 : (0 : ℕ) ∉ hits n (· < n) := by
    simp [hits, trajectory]
  have heq : hits n (· ≤ n) = insert 0 (hits n (· < n)) := by
    ext i
    simp only [hits, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨hi, hle⟩
      by_cases h0i : i = 0
      · exact Or.inl h0i
      · right
        refine ⟨hi, ?_⟩
        have hne := key 0 i (by omega) (by omega)
        have h00 : trajectory n 0 = n := rfl
        omega
    · rintro (rfl | ⟨hi, hlt⟩)
      · exact ⟨by omega, le_refl n⟩
      · exact ⟨hi, le_of_lt hlt⟩
  rw [heq, Finset.card_insert_of_notMem h0]
  omega
