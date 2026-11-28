import OMAStatements.S_oeis_a103621
import Mathlib

open OMA.S_oeis_a103621

namespace P103621

theorem hiZ (n i : ℕ) (hi6 : 6 ≤ i) (hil : i < n.log2 + 1)
    (hS : n % 64 = 9 ∨ n % 64 = 11 ∨ n % 64 = 13 ∨ n % 64 = 23 ∨ n % 64 = 25 ∨ n % 64 = 27 ∨ n % 64 = 61 ∨ n % 64 = 7) (hn : n < 2 ^ 37 - 37) :
    ¬ ((n + (i + 1)) % 2 ^ (i + 1) = 0) := by
  intro h0
  have hd : 2 ^ (i + 1) ∣ n + (i + 1) := Nat.dvd_of_mod_eq_zero h0
  have h64 : 64 ∣ n + (i + 1) := by
    have : (64 : ℕ) ∣ 2 ^ (i + 1) := by
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)
    exact this.trans hd
  have hn0 : n ≠ 0 := by omega
  have h2i : 2 ^ i ≤ n := by
    have := Nat.log2_self_le hn0
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) this
  have hi37 : i < 37 := by
    by_contra hc
    have : 2 ^ 37 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk : i + 1 = 37 := by omega
  rw [hk] at hd
  have hpos : 0 < n + 37 := by omega
  have := Nat.le_of_dvd hpos hd
  norm_num at hn this
  omega

theorem sl9 (n : ℕ) (h64 : 64 ≤ n) (hr : n % 64 = 9) (hn : n < 2 ^ 37 - 37) :
    sloping n = n + 2 := by
  unfold sloping
  have hL : 6 ≤ n.log2 := by
    have := (Nat.log2_lt (show n ≠ 0 by omega) (k := 6)).not.mpr (by omega)
    omega
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show 6 ≤ n.log2 + 1 by omega))]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num only
    simp (disch := omega) only [if_pos, if_neg]
    try omega
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [if_neg (hiZ n i (by omega) hi (by omega) hn)]

theorem sl11 (n : ℕ) (h64 : 64 ≤ n) (hr : n % 64 = 11) (hn : n < 2 ^ 37 - 37) :
    sloping n = n + 2 := by
  unfold sloping
  have hL : 6 ≤ n.log2 := by
    have := (Nat.log2_lt (show n ≠ 0 by omega) (k := 6)).not.mpr (by omega)
    omega
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show 6 ≤ n.log2 + 1 by omega))]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num only
    simp (disch := omega) only [if_pos, if_neg]
    try omega
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [if_neg (hiZ n i (by omega) hi (by omega) hn)]

theorem sl13 (n : ℕ) (h64 : 64 ≤ n) (hr : n % 64 = 13) (hn : n < 2 ^ 37 - 37) :
    sloping n = n + 10 := by
  unfold sloping
  have hL : 6 ≤ n.log2 := by
    have := (Nat.log2_lt (show n ≠ 0 by omega) (k := 6)).not.mpr (by omega)
    omega
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show 6 ≤ n.log2 + 1 by omega))]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num only
    simp (disch := omega) only [if_pos, if_neg]
    try omega
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [if_neg (hiZ n i (by omega) hi (by omega) hn)]

theorem sl23 (n : ℕ) (h64 : 64 ≤ n) (hr : n % 64 = 23) (hn : n < 2 ^ 37 - 37) :
    sloping n = n + 2 := by
  unfold sloping
  have hL : 6 ≤ n.log2 := by
    have := (Nat.log2_lt (show n ≠ 0 by omega) (k := 6)).not.mpr (by omega)
    omega
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show 6 ≤ n.log2 + 1 by omega))]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num only
    simp (disch := omega) only [if_pos, if_neg]
    try omega
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [if_neg (hiZ n i (by omega) hi (by omega) hn)]

theorem sl25 (n : ℕ) (h64 : 64 ≤ n) (hr : n % 64 = 25) (hn : n < 2 ^ 37 - 37) :
    sloping n = n + 2 := by
  unfold sloping
  have hL : 6 ≤ n.log2 := by
    have := (Nat.log2_lt (show n ≠ 0 by omega) (k := 6)).not.mpr (by omega)
    omega
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show 6 ≤ n.log2 + 1 by omega))]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num only
    simp (disch := omega) only [if_pos, if_neg]
    try omega
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [if_neg (hiZ n i (by omega) hi (by omega) hn)]

theorem sl27 (n : ℕ) (h64 : 64 ≤ n) (hr : n % 64 = 27) (hn : n < 2 ^ 37 - 37) :
    sloping n = n + 34 := by
  unfold sloping
  have hL : 6 ≤ n.log2 := by
    have := (Nat.log2_lt (show n ≠ 0 by omega) (k := 6)).not.mpr (by omega)
    omega
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show 6 ≤ n.log2 + 1 by omega))]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num only
    simp (disch := omega) only [if_pos, if_neg]
    try omega
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [if_neg (hiZ n i (by omega) hi (by omega) hn)]

theorem sl61 (n : ℕ) (h64 : 64 ≤ n) (hr : n % 64 = 61) (hn : n < 2 ^ 37 - 37) :
    sloping n = n + 10 := by
  unfold sloping
  have hL : 6 ≤ n.log2 := by
    have := (Nat.log2_lt (show n ≠ 0 by omega) (k := 6)).not.mpr (by omega)
    omega
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show 6 ≤ n.log2 + 1 by omega))]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num only
    simp (disch := omega) only [if_pos, if_neg]
    try omega
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [if_neg (hiZ n i (by omega) hi (by omega) hn)]

theorem sl7 (n : ℕ) (h64 : 64 ≤ n) (hr : n % 64 = 7) (hn : n < 2 ^ 37 - 37) :
    sloping n = n + 2 := by
  unfold sloping
  have hL : 6 ≤ n.log2 := by
    have := (Nat.log2_lt (show n ≠ 0 by omega) (k := 6)).not.mpr (by omega)
    omega
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show 6 ≤ n.log2 + 1 by omega))]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num only
    simp (disch := omega) only [if_pos, if_neg]
    try omega
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [if_neg (hiZ n i (by omega) hi (by omega) hn)]


theorem o9 : orbit 9 = 73 := by decide

theorem chain6 (t : ℕ) (h1 : 1 ≤ t) (hb : 64 * t + 25 < 137438953435) (h : orbit (8 * t + 1) = 9 + 64 * t) :
    orbit (8 * t + 6) = 27 + 64 * t := by
  have B : (2 : ℕ) ^ 37 - 37 = 137438953435 := by norm_num
  have e2 : orbit (8 * t + 2) = 11 + 64 * t := by
    show sloping (orbit (8 * t + 1)) = _
    rw [h, sl9 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  have e3 : orbit (8 * t + 3) = 13 + 64 * t := by
    show sloping (orbit (8 * t + 2)) = _
    rw [e2, sl11 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  have e4 : orbit (8 * t + 4) = 23 + 64 * t := by
    show sloping (orbit (8 * t + 3)) = _
    rw [e3, sl13 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  have e5 : orbit (8 * t + 5) = 25 + 64 * t := by
    show sloping (orbit (8 * t + 4)) = _
    rw [e4, sl23 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  have e6 : orbit (8 * t + 6) = 27 + 64 * t := by
    show sloping (orbit (8 * t + 5)) = _
    rw [e5, sl25 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  exact e6

theorem chain (t : ℕ) (h1 : 1 ≤ t) (hb : 64 * t + 71 < 137438953435) (h : orbit (8 * t + 1) = 9 + 64 * t) :
    orbit (8 * t + 2) = 11 + 64 * t ∧ orbit (8 * t + 3) = 13 + 64 * t ∧
    orbit (8 * t + 4) = 23 + 64 * t ∧ orbit (8 * t + 5) = 25 + 64 * t ∧
    orbit (8 * t + 6) = 27 + 64 * t ∧ orbit (8 * t + 7) = 61 + 64 * t ∧
    orbit (8 * t + 8) = 71 + 64 * t ∧ orbit (8 * (t + 1) + 1) = 9 + 64 * (t + 1) := by
  have B : (2 : ℕ) ^ 37 - 37 = 137438953435 := by norm_num
  have e2 : orbit (8 * t + 2) = 11 + 64 * t := by
    show sloping (orbit (8 * t + 1)) = _
    rw [h, sl9 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  have e3 : orbit (8 * t + 3) = 13 + 64 * t := by
    show sloping (orbit (8 * t + 2)) = _
    rw [e2, sl11 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  have e4 : orbit (8 * t + 4) = 23 + 64 * t := by
    show sloping (orbit (8 * t + 3)) = _
    rw [e3, sl13 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  have e5 : orbit (8 * t + 5) = 25 + 64 * t := by
    show sloping (orbit (8 * t + 4)) = _
    rw [e4, sl23 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  have e6 : orbit (8 * t + 6) = 27 + 64 * t := by
    show sloping (orbit (8 * t + 5)) = _
    rw [e5, sl25 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  have e7 : orbit (8 * t + 7) = 61 + 64 * t := by
    show sloping (orbit (8 * t + 6)) = _
    rw [e6, sl27 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  have e8 : orbit (8 * t + 8) = 71 + 64 * t := by
    show sloping (orbit (8 * t + 7)) = _
    rw [e7, sl61 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  have e9 : orbit (8 * (t + 1) + 1) = 9 + 64 * (t + 1) := by
    rw [show 8 * (t + 1) + 1 = (8 * t + 8) + 1 by ring]
    show sloping (orbit (8 * t + 8)) = _
    rw [e8, sl7 _ (by omega) (by omega) (by rw [B]; omega)]; ring
  exact ⟨e2, e3, e4, e5, e6, e7, e8, e9⟩

theorem per : ∀ t, 1 ≤ t → t ≤ 2147483647 → orbit (8 * t + 1) = 9 + 64 * t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro _; exact o9
  | succ t ht ih =>
    intro hle
    exact (chain t ht (by omega) (ih (by omega))).2.2.2.2.2.2.2

theorem hiX (i : ℕ) (hi6 : 6 ≤ i) (hil : i < 36) :
    ¬ ((137438953435 + (i + 1)) % 2 ^ (i + 1) = 0) := by
  intro h0
  have hd : 2 ^ (i + 1) ∣ 137438953435 + (i + 1) := Nat.dvd_of_mod_eq_zero h0
  have : (64 : ℕ) ∣ 2 ^ (i + 1) := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)
  have := this.trans hd
  omega

theorem slx : sloping 137438953435 = 137438953435 + 34 + 2 ^ 37 := by
  unfold sloping
  have hL : Nat.log2 137438953435 = 36 := by
    rw [Nat.log2_eq_iff (by norm_num)]; norm_num
  rw [hL, Finset.sum_range_succ]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show 6 ≤ 36 by omega))]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [if_neg (hiX i (by omega) hi)]

end P103621

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a103621.main) := by
  intro h
  have h1 := h.1 17179869184 (by norm_num)
  have c1 := P103621.chain 2147483646 (by norm_num) (by norm_num) (P103621.per 2147483646 (by norm_num) (by norm_num))
  have b6 := P103621.chain6 2147483647 (by norm_num) (by norm_num) (P103621.per 2147483647 (by norm_num) (by norm_num))
  obtain ⟨-, -, -, -, a6, a7, -, -⟩ := c1
  norm_num at a6 a7 b6
  have b7 : orbit 17179869183 = 137438953435 + 34 + 2 ^ 37 := by
    show sloping (orbit 17179869182) = _
    rw [b6, P103621.slx]
  have e1 : a 17179869184 = orbit 17179869183 := rfl
  have e2 : a (17179869184 - 9) = orbit 17179869174 := rfl
  have e3 : a (17179869184 - 1) = orbit 17179869182 := rfl
  have e4 : a (17179869184 - 8) = orbit 17179869175 := rfl
  rw [e1, e2, e3, e4, b7, b6, a6, a7] at h1
  norm_num at h1
