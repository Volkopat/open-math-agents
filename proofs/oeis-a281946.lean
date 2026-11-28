import OMAStatements.S_oeis_a281946
import Mathlib

namespace OMA.S_oeis_a281946

def F (n : ℕ) : ℚ := ∑ m ∈ Finset.range (n + 1), (((n + 1 - m).choose 2 : ℕ) : ℚ) / (m.factorial : ℚ)

def E (n : ℕ) : ℚ := ∑ m ∈ Finset.range (n + 1), 1 / (m.factorial : ℚ)

def G (n : ℕ) : ℚ := ∑ m ∈ Finset.range n, ((n + 1 - m : ℕ) : ℚ) / (m.factorial : ℚ)

theorem a_eq_F (n : ℕ) : b n = n.factorial * F n := by
  unfold b F
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

def w (k : ℕ) : ℚ := ((k.choose 3 : ℕ) : ℚ) + 3 * ((k.choose 4 : ℕ) : ℚ)

def H (n : ℕ) : ℚ := ∑ m ∈ Finset.range (n + 1), w (n + 2 - m) / (m.factorial : ℚ)

def K (n : ℕ) : ℚ := ∑ m ∈ Finset.range (n + 1), (((n + 2 - m).choose 3 : ℕ) : ℚ) / (m.factorial : ℚ)

theorem F_closed (n : ℕ) : 2 * F n = ((n : ℚ) ^ 2 - n + 1) * E n + (n - 1) / (n.factorial : ℚ) := by
  induction n with
  | zero => simp [F, E]
  | succ n ih =>
    rw [F_succ, E_succ]
    have hf : ((n + 1).factorial : ℚ) = (n + 1) * n.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hk : (n.factorial : ℚ) ≠ 0 := by positivity
    rw [hf]
    push_cast
    field_simp
    field_simp at ih
    linear_combination (n + 1) * ih

theorem K_succ (n : ℕ) : K (n + 1) = K n + F (n + 1) := by
  have e1 := Finset.sum_range_succ (fun m => (((n + 1 + 2 - m).choose 3 : ℕ) : ℚ) / (m.factorial : ℚ)) (n + 1)
  have e2 := Finset.sum_range_succ (fun m => (((n + 1 + 1 - m).choose 2 : ℕ) : ℚ) / (m.factorial : ℚ)) (n + 1)
  beta_reduce at e1 e2
  unfold K F
  rw [e1, e2]
  have h1 : n + 1 + 2 - (n + 1) = 2 := by omega
  have h2 : n + 1 + 1 - (n + 1) = 1 := by omega
  rw [h1, h2]
  simp only [Nat.choose_eq_zero_of_lt (show 2 < 3 by norm_num), Nat.choose_eq_zero_of_lt (show 1 < 2 by norm_num), Nat.cast_zero, zero_div, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  have : n + 1 + 2 - m = (n + 1 + 1 - m) + 1 := by omega
  have h3 : n + 1 + 2 - m = (n + 2 - m) + 1 := by omega
  have h4 : n + 1 + 1 - m = n + 2 - m := by omega
  rw [h3, h4, Nat.choose_succ_succ (n + 2 - m) 2]
  push_cast; ring


theorem K_eq (n : ℕ) : 3 * K n = n * F (n + 1) - F n := by
  induction n with
  | zero => simp [K, F]
  | succ n ih =>
    have hc := F_closed n
    have s1 := F_succ n
    have s2 := F_succ (n + 1)
    have s3 := E_succ n
    have hf : ((n + 1).factorial : ℚ) = (n + 1) * n.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hk : (n.factorial : ℚ) ≠ 0 := by positivity
    rw [K_succ, mul_add]
    have hFn : F n = (((n : ℚ) ^ 2 - n + 1) * E n + (n - 1) / (n.factorial : ℚ)) / 2 := by linarith
    have e : 3 * K n = n * F (n + 1) - F n := ih
    rw [e, s2, s3, s1, hf, hFn]
    push_cast
    field_simp
    ring

theorem w_succ (k : ℕ) : w (k + 1) = w k + ((k.choose 2 : ℕ) : ℚ) + 3 * ((k.choose 3 : ℕ) : ℚ) := by
  have a : (k + 1).choose 3 = k.choose 2 + k.choose 3 := Nat.choose_succ_succ k 2
  have b : (k + 1).choose 4 = k.choose 3 + k.choose 4 := Nat.choose_succ_succ k 3
  unfold w
  rw [a, b]
  push_cast
  ring

theorem H_succ (n : ℕ) : H (n + 1) = H n + F (n + 1) + 3 * K n := by
  have e1 := Finset.sum_range_succ (fun m => w (n + 1 + 2 - m) / (m.factorial : ℚ)) (n + 1)
  beta_reduce at e1
  unfold H K
  rw [e1]
  have h1 : n + 1 + 2 - (n + 1) = 2 := by omega
  rw [h1]
  have hw : w 2 = 0 := by unfold w; norm_num [Nat.choose_eq_zero_of_lt]
  rw [hw, zero_div, add_zero, Finset.mul_sum]
  have hF : F (n + 1) = ∑ m ∈ Finset.range (n + 1), (((n + 1 + 1 - m).choose 2 : ℕ) : ℚ) / (m.factorial : ℚ) := by
    unfold F
    rw [Finset.sum_range_succ _ (n + 1)]
    have : n + 1 + 1 - (n + 1) = 1 := by omega
    rw [this]; simp
  rw [hF, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  have h3 : n + 1 + 2 - m = (n + 2 - m) + 1 := by omega
  have h4 : n + 1 + 1 - m = n + 2 - m := by omega
  rw [h3, h4]
  rw [w_succ]
  ring


theorem w_small (k : ℕ) (hk : k < 3) : w k = 0 := by
  unfold w
  rw [Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt (by omega : k < 4)]
  simp

theorem a_eq_H (n : ℕ) : a n = n.factorial * H n := by
  unfold a H
  congr 1
  have h1 : ∑ k ∈ Finset.Icc 3 (n + 2), (((k.choose 3 : ℕ) : ℚ) + 3 * ((k.choose 4 : ℕ) : ℚ)) / ((n + 2 - k).factorial : ℚ)
      = ∑ k ∈ Finset.range (n + 3), w k / ((n + 2 - k).factorial : ℚ) := by
    have : Finset.range (n + 3) = insert 0 (insert 1 (insert 2 (Finset.Icc 3 (n + 2)))) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [this, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    rw [w_small 0 (by norm_num), w_small 1 (by norm_num), w_small 2 (by norm_num)]
    simp [w]
  rw [h1, ← Finset.sum_range_reflect, Finset.sum_range_succ _ (n + 2), Finset.sum_range_succ _ (n + 1)]
  have h2 : n + 3 - 1 - (n + 2) = 0 := by omega
  have h3 : n + 3 - 1 - (n + 1) = 1 := by omega
  rw [h2, h3, w_small 0 (by norm_num), w_small 1 (by norm_num)]
  simp only [zero_div, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  have h4 : n + 3 - 1 - m = n + 2 - m := by omega
  have h5 : n + 2 - (n + 2 - m) = m := by omega
  rw [h4, h5]

theorem H_rec (n : ℕ) : H (n + 1) = H n + (n + 1) * F (n + 1) - F n := by
  rw [H_succ]
  have := K_eq n
  linarith

theorem part2 (n : ℕ) (hn : 2 ≤ n) : a n = (n : ℚ) * (a (n - 1) + b n - b (n - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [a_eq_H, a_eq_H, a_eq_F, a_eq_F, H_rec]
  have hf : ((k + 1).factorial : ℚ) = (k + 1) * k.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hf]
  push_cast
  ring

theorem S1 (j : ℕ) : Nat.stirlingSecond (j + 2) (j + 1) = (j + 2).choose 2 := by
  induction j with
  | zero => decide
  | succ m ih =>
    rw [Nat.stirlingSecond_succ_succ, Nat.stirlingSecond_self, ih, Nat.choose_succ_succ (m + 2) 1]
    simp [Nat.choose_one_right]

theorem S2 (j : ℕ) : Nat.stirlingSecond (j + 2) j = (j + 2).choose 3 + 3 * (j + 2).choose 4 := by
  induction j with
  | zero => decide
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, Nat.stirlingSecond_succ_succ, S1, ih]
    have key : 3 * (m + 2).choose 3 = m * (m + 2).choose 2 := by
      have h : (m + 2).choose 3 * 3 = (m + 2).choose 2 * m := by
        simpa using Nat.choose_succ_right_eq (m + 2) 2
      linarith
    have a : (m + 2 + 1).choose 3 = (m + 2).choose 2 + (m + 2).choose 3 := Nat.choose_succ_succ (m + 2) 2
    have b : (m + 2 + 1).choose 4 = (m + 2).choose 3 + (m + 2).choose 4 := Nat.choose_succ_succ (m + 2) 3
    rw [a, b]
    nlinarith [key]

theorem H_refl (n : ℕ) : H n = ∑ j ∈ Finset.range (n + 1), w (j + 2) / ((n - j).factorial : ℚ) := by
  unfold H
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  have h2 : n + 1 - 1 - m = n - m := by omega
  have h3 : n + 2 - (n + 1 - 1 - m) = m + 2 := by omega
  rw [h3, h2]

theorem part1 (n : ℕ) : a n = 3 * A 2 n / (((n + 2).choose 2 : ℕ) : ℚ) := by
  rw [a_eq_H, H_refl]
  unfold A
  have hf : ((2 + n).factorial : ℚ) = (n + 2) * (n + 1) * n.factorial := by
    rw [add_comm, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have h2 : ((2 + 1).factorial : ℚ) = 6 := by norm_num [Nat.factorial]
  have : ∀ j ∈ Finset.range (n + 1), ((2 + n).factorial : ℚ) * (Nat.stirlingSecond (2 + j) j : ℚ) / ((n - j).factorial : ℚ)
      = ((2 + n).factorial : ℚ) * (w (j + 2) / ((n - j).factorial : ℚ)) := by
    intro j _
    rw [mul_div_assoc, add_comm 2 j, S2]
    unfold w
    push_cast
    ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hf, h2, Nat.cast_choose_two]
  generalize (∑ j ∈ Finset.range (n + 1), w (j + 2) / ((n - j).factorial : ℚ)) = S
  push_cast
  have hn : ((n : ℚ) + 2) * (n + 1) ≠ 0 := by positivity
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℚ) + 2 ≠ 0 := by positivity
  have hn3 : (1 : ℚ) + n ≠ 0 := by positivity
  have hinv : (1 + (n : ℚ))⁻¹ * (1 + n) = 1 := inv_mul_cancel₀ hn3
  field_simp
  linear_combination (-6 * S) * hinv

end OMA.S_oeis_a281946

theorem OMA.solution : type_of% @OMA.S_oeis_a281946.main := by
  exact ⟨fun n hn => OMA.S_oeis_a281946.part1 n, fun n hn => OMA.S_oeis_a281946.part2 n hn⟩
