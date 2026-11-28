import OMAStatements.S_oeis_a281912
import Mathlib

namespace OMA.S_oeis_a281912

def F (n : ℕ) : ℚ := ∑ m ∈ Finset.range (n + 1), (((n + 1 - m).choose 2 : ℕ) : ℚ) / (m.factorial : ℚ)

def E (n : ℕ) : ℚ := ∑ m ∈ Finset.range (n + 1), 1 / (m.factorial : ℚ)

def G (n : ℕ) : ℚ := ∑ m ∈ Finset.range n, ((n + 1 - m : ℕ) : ℚ) / (m.factorial : ℚ)

theorem a_eq_F (n : ℕ) : a n = n.factorial * F n := by
  unfold a F
  congr 1
  have h1 : ∑ k ∈ Finset.Icc 2 (n + 1), ((k.choose 2 : ℕ) : ℚ) / ((n + 1 - k).factorial : ℚ)
      = ∑ k ∈ Finset.range (n + 2), ((k.choose 2 : ℕ) : ℚ) / ((n + 1 - k).factorial : ℚ) := by
    have : Finset.range (n + 2) = insert 0 (insert 1 (Finset.Icc 2 (n + 1))) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [this, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    simp
  rw [h1, ← Finset.sum_range_reflect]
  rw [Finset.sum_range_succ (n := n + 1)]
  have h0 : n + 2 - 1 - (n + 1) = 0 := by omega
  rw [h0]
  simp only [Nat.choose_zero_succ, Nat.cast_zero, zero_div, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  have h2 : n + 2 - 1 - m = n + 1 - m := by omega
  rw [h2]
  have : n + 1 - (n + 1 - m) = m := by omega
  rw [this]

theorem E_succ (n : ℕ) : E (n + 1) = E n + 1 / ((n + 1).factorial : ℚ) := by
  unfold E; rw [Finset.sum_range_succ]

theorem G_succ (n : ℕ) : G (n + 1) = G n + (E n - 1 / (n.factorial : ℚ)) + 2 / (n.factorial : ℚ) := by
  have hE : E n - 1 / (n.factorial : ℚ) = ∑ m ∈ Finset.range n, 1 / (m.factorial : ℚ) := by
    unfold E; rw [Finset.sum_range_succ]; ring
  rw [hE]
  unfold G
  rw [Finset.sum_range_succ (n := n)]
  have : ∀ m ∈ Finset.range n, ((n + 1 + 1 - m : ℕ) : ℚ) / (m.factorial : ℚ)
      = ((n + 1 - m : ℕ) : ℚ) / (m.factorial : ℚ) + 1 / (m.factorial : ℚ) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have : n + 1 + 1 - m = (n + 1 - m) + 1 := by omega
    rw [this]; push_cast; ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  have : ((n + 1 + 1 - n : ℕ) : ℚ) = 2 := by
    have : n + 1 + 1 - n = 2 := by omega
    rw [this]; norm_num
  rw [this]
  try ring

theorem G_eq (n : ℕ) : G n = n * E n := by
  induction n with
  | zero => simp [G, E]
  | succ n ih =>
    rw [G_succ, ih, E_succ]
    have : ((n + 1).factorial : ℚ) = (n + 1) * n.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hn : (n.factorial : ℚ) ≠ 0 := by positivity
    rw [this]
    push_cast
    field_simp
    ring

theorem F_succ (n : ℕ) : F (n + 1) = F n + (n * E n + 1 / (n.factorial : ℚ)) := by
  rw [← G_eq]
  unfold F G
  rw [Finset.sum_range_succ _ (n + 1)]
  have : ∀ m ∈ Finset.range (n + 1), (((n + 1 + 1 - m).choose 2 : ℕ) : ℚ) / (m.factorial : ℚ)
      = (((n + 1 - m).choose 2 : ℕ) : ℚ) / (m.factorial : ℚ) + ((n + 1 - m : ℕ) : ℚ) / (m.factorial : ℚ) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have : n + 1 + 1 - m = (n + 1 - m) + 1 := by omega
    rw [this, Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    push_cast; ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ (n := n) (f := fun m => ((n + 1 - m : ℕ) : ℚ) / (m.factorial : ℚ))]
  simp
  try ring

theorem e_eq (n : ℕ) : e n = n.factorial * E n := by
  unfold e E
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [div_eq_mul_one_div]

theorem S_aux (k : ℕ) : Nat.stirlingSecond (k + 2) (k + 1) = (k + 2).choose 2 := by
  induction k with
  | zero => decide
  | succ m ih =>
    rw [Nat.stirlingSecond_succ_succ, Nat.stirlingSecond_self, ih, Nat.choose_succ_succ (m + 2) 1]
    simp [Nat.choose_one_right]

theorem S_succ (j : ℕ) : (Nat.stirlingSecond (1 + j) j : ℚ) = ((j + 1).choose 2 : ℕ) := by
  rcases j with _ | k
  · simp
  · rw [show 1 + (k + 1) = k + 2 by omega, S_aux]

theorem F_refl (n : ℕ) : F n = ∑ j ∈ Finset.range (n + 1), (((j + 1).choose 2 : ℕ) : ℚ) / ((n - j).factorial : ℚ) := by
  unfold F
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  have h2 : n + 1 - 1 - m = n - m := by omega
  rw [h2]
  have : n + 1 - (n - m) = m + 1 := by omega
  rw [this]

theorem part1 (n : ℕ) : a n = 2 * A 1 n / ((n : ℚ) + 1) := by
  rw [a_eq_F, F_refl]
  unfold A
  have hf : ((1 + n).factorial : ℚ) = (n + 1) * n.factorial := by
    rw [add_comm, Nat.factorial_succ]; push_cast; ring
  have h2 : ((1 + 1).factorial : ℚ) = 2 := by norm_num [Nat.factorial]
  have : ∀ j ∈ Finset.range (n + 1), ((1 + n).factorial : ℚ) * (Nat.stirlingSecond (1 + j) j : ℚ) / ((n - j).factorial : ℚ)
      = ((1 + n).factorial : ℚ) * ((((j + 1).choose 2 : ℕ) : ℚ) / ((n - j).factorial : ℚ)) := by
    intro j _
    rw [S_succ, mul_div_assoc]
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hf, h2]
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  field_simp

theorem part2 (n : ℕ) (hn : 2 ≤ n) : a n = (n : ℚ) * (a (n - 1) + e n - e (n - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [a_eq_F, a_eq_F, e_eq, e_eq, F_succ, E_succ]
  have hf : ((k + 1).factorial : ℚ) = (k + 1) * k.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  rw [hf]
  push_cast
  field_simp
  ring

end OMA.S_oeis_a281912

theorem OMA.solution : type_of% @OMA.S_oeis_a281912.main := by
  exact ⟨fun n hn => OMA.S_oeis_a281912.part1 n, fun n hn => OMA.S_oeis_a281912.part2 n hn⟩
