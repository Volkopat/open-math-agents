import OMAStatements.S_oeis_a158233

namespace OMA.S_oeis_a158233





theorem pos_inv (i : ℕ) : 1 ≤ (pos i).2 ∧ (pos i).2 < (pos i).1 := by
  induction i with
  | zero => simp [pos]
  | succ i ih =>
    simp only [pos, next]
    split_ifs with h
    · simp only
      omega
    · simp only
      omega

def S9 : Finset (ZMod 9) := {0, 3, 4, 6}

theorem res_row : ∀ x y : ZMod 9, (x ^ 2 - y ^ 2) * (x ^ 2 - (y + 1) ^ 2) ∈ S9 := by
  decide +kernel

theorem res_cross : ∀ x : ZMod 9, (x ^ 2 - (x - 1) ^ 2) * ((x + 1) ^ 2 - 1) ∈ S9 := by
  decide +kernel

theorem val_mem {z : ZMod 9} (h : z ∈ S9) : z.val = 0 ∨ z.val = 3 ∨ z.val = 4 ∨ z.val = 6 := by
  revert z
  decide +kernel

/-- The conjecture: every term is 0, 3, 4 or 6. -/
theorem conjecture (n : ℕ) (hn : 1 ≤ n) : a n = 0 ∨ a n = 3 ∨ a n = 4 ∨ a n = 6 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hinv := pos_inv j
  have hT1 : T (j + 1 + 1) = (pos j).1 ^ 2 - (pos j).2 ^ 2 := by simp [T]
  have hT2 : T (j + 1 + 2) = (next (pos j)).1 ^ 2 - (next (pos j)).2 ^ 2 := by
    simp [T, show j + 1 + 2 - 2 = j + 1 by omega, pos]
  have hval : ∀ P : ℕ, P % 9 = ((P : ZMod 9)).val := fun P => (ZMod.val_natCast 9 P).symm
  unfold a
  rw [hT1, hT2, hval]
  apply val_mem
  generalize pos j = mk at hinv ⊢
  obtain ⟨m, k⟩ := mk
  simp only at hinv ⊢
  have hk2 : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hinv.2.le 2
  unfold next
  split_ifs with h
  · simp only
    have hk3 : (k + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (by omega) 2
    rw [Nat.cast_mul, Nat.cast_sub hk2, Nat.cast_sub hk3]
    push_cast
    exact res_row (m : ZMod 9) (k : ZMod 9)
  · simp only
    have hkm : k = m - 1 := by omega
    have h1 : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hm1 : (m - 1 : ℕ) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (by omega) 2
    simp only [one_pow]
    rw [hkm, Nat.cast_mul, Nat.cast_sub hm1, Nat.cast_sub h1]
    push_cast [show 1 ≤ m by omega]
    exact res_cross (m : ZMod 9)

end OMA.S_oeis_a158233

theorem OMA.solution : type_of% @OMA.S_oeis_a158233.main :=
  fun n hn => OMA.S_oeis_a158233.conjecture n hn
