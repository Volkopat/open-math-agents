import OMAStatements.S_oeis_a286050

open OMA.S_oeis_a286050

namespace ThueMorseZeros

private theorem tm_pair (j : ℕ) : tm (2*j) + tm (2*j+1) = 1 := by
  have h : Nat.digits 2 (2*j+1) = 1 :: Nat.digits 2 j := by
    simpa [Nat.add_comm] using Nat.digits_add 2 (by decide) 1 j (by decide) (Or.inl (by decide))
  by_cases hz : j = 0
  · subst j
    decide
  · unfold tm
    rw [h, Nat.digits_base_mul (by decide) (Nat.pos_of_ne_zero hz)]
    simp only [List.count_cons, beq_self_eq_true, show (0 == (1 : ℕ)) = false by decide,
      Bool.false_eq_true, ↓reduceIte, add_zero]
    omega

private theorem first_copied (k j : ℕ) (h : pos (2*k) = 2*j) :
    pos (2*k+1) = 2*j+1 := by
  have hp := tm_pair j
  rw [pos, h, if_neg]
  omega

private theorem at_pair (k : ℕ) : ∃ j, pos (2*k) = 2*j := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨j,hj⟩ := ih
    rw [show 2*(k+1) = (2*k+1)+1 by omega, pos, first_copied k j hj]
    split
    · exact ⟨j+2, by omega⟩
    · exact ⟨j+1, by omega⟩

private theorem w_pair (k : ℕ) : w (2*k) + w (2*k+1) = 1 := by
  obtain ⟨j,hj⟩ := at_pair k
  simpa only [w, hj, first_copied k j hj] using tm_pair j

private theorem count_pairs (k : ℕ) : Nat.count (fun i => w i = 0) (2*k) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1) = (2*k+1)+1 by omega, Nat.count_succ, Nat.count_succ, ih]
    have hp := w_pair k
    split_ifs <;> omega

private theorem nth_zero (k : ℕ) :
    Nat.nth (fun i => w i = 0) k = 2*k ∨ Nat.nth (fun i => w i = 0) k = 2*k+1 := by
  have hc := count_pairs k
  by_cases hz : w (2*k) = 0
  · left
    simpa only [hc] using Nat.nth_count (p := fun i => w i = 0) hz
  · have hp := w_pair k
    have h₁ : w (2*k+1) = 0 := by omega
    have hc' : Nat.count (fun i => w i = 0) (2*k+1) = k := by
      rw [Nat.count_succ, hc, if_neg hz, add_zero]
    right
    simpa only [hc'] using Nat.nth_count (p := fun i => w i = 0) h₁

theorem result (n : ℕ) (hn : 1 ≤ n) :
    2 * (n : ℤ) - a n = 0 ∨ 2 * (n : ℤ) - a n = 1 := by
  unfold a
  rcases nth_zero (n-1) with h | h <;> omega

end ThueMorseZeros

theorem OMA.solution : type_of% @OMA.S_oeis_a286050.main := ThueMorseZeros.result
