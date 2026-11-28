import OMAStatements.S_oeis_a196020

-- Problem: A196020, T(n,k) = P(n,k)^2 - P(n-1,k)^2. With t = k(k+1)/2, a sum of k consecutive parts
-- starting at a is k a + k(k-1)/2 = k (a-1) + t, so consecParts m k = 1 iff t <= m and k | m - t (else 0).
-- Hence P(n,k) = (n - t)/k + 1 for n >= t (induction, using (a+1)/k = a/k + [k | a+1]), so
-- P(n)^2 - P(n-1)^2 is 0 unless k | n - t, and then equals 2 P(n) - 1 = 2 (n - t)/k + 1.

namespace OMA.A196020

open OMA.S_oeis_a196020 Finset

lemma t_eq (k : ℕ) : k * (k + 1) / 2 = (∑ i ∈ range k, i) + k := by
  have h := Finset.sum_range_id_mul_two (k + 1)
  rw [Finset.sum_range_succ] at h
  rw [show k * (k + 1) = (k + 1) * (k + 1 - 1) by rw [Nat.add_sub_cancel, mul_comm], ← h]
  omega

lemma sum_consec (a k : ℕ) : ∑ i ∈ range k, (a + i) = k * a + ∑ i ∈ range k, i := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]

lemma consec_eq (m k : ℕ) (hk : 1 ≤ k) :
    consecParts m k = if k * (k + 1) / 2 ≤ m ∧ k ∣ m - k * (k + 1) / 2 then 1 else 0 := by
  unfold consecParts
  rw [t_eq]
  set s := ∑ i ∈ range k, i
  simp_rw [sum_consec]
  split_ifs with h
  · obtain ⟨h1, q, hq⟩ := h
    rw [Finset.card_eq_one]
    refine ⟨q + 1, ?_⟩
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨-, ha⟩
      have : k * a = k * (q + 1) := by rw [mul_add, mul_one]; omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    · rintro rfl
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · have : q + 1 ≤ k * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
        rw [mul_add, mul_one] at this; omega
      · rw [mul_add, mul_one]; omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro a ha hsum
    have ha1 := (Finset.mem_Icc.mp ha).1
    apply h
    refine ⟨?_, a - 1, ?_⟩
    · have : k ≤ k * a := Nat.le_mul_of_pos_right _ ha1
      omega
    · rw [Nat.mul_sub, mul_one]
      have : k ≤ k * a := Nat.le_mul_of_pos_right _ ha1
      omega

lemma P_eq (n k : ℕ) (hk : 1 ≤ k) :
    P n k = if k * (k + 1) / 2 ≤ n then (n - k * (k + 1) / 2) / k + 1 else 0 := by
  set t := k * (k + 1) / 2 with htdef
  have ht1 : 1 ≤ t := by rw [htdef, t_eq]; omega
  induction n with
  | zero => simp [P]; omega
  | succ n ih =>
    unfold P at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), ih, consec_eq _ _ hk, ← htdef]
    by_cases h1 : t ≤ n
    · have h2 : t ≤ n + 1 := by omega
      rw [if_pos h1, if_pos h2, show n + 1 - t = (n - t) + 1 by omega, Nat.succ_div]
      by_cases hd : k ∣ n - t + 1
      · rw [if_pos ⟨h2, hd⟩, if_pos hd]
      · rw [if_neg (fun h => hd h.2), if_neg hd]
    · rw [if_neg h1]
      by_cases h2 : t ≤ n + 1
      · have he : n + 1 = t := by omega
        rw [if_pos h2, he, Nat.sub_self, Nat.zero_div, if_pos ⟨le_rfl, dvd_zero k⟩]
      · rw [if_neg h2, if_neg (fun h => h2 h.1)]

end OMA.A196020

theorem OMA.solution : type_of% @OMA.S_oeis_a196020.main := by
  intro n k hn hk htn
  have ht1 : 1 ≤ k * (k + 1) / 2 := by rw [OMA.A196020.t_eq]; omega
  rw [OMA.A196020.P_eq n k hk, OMA.A196020.P_eq (n - 1) k hk, if_pos htn]
  unfold OMA.S_oeis_a196020.T
  set t := k * (k + 1) / 2 with htdef
  by_cases heq : n = t
  · rw [if_neg (show ¬ t ≤ n - 1 by omega),
      if_pos ⟨htn, by rw [heq, Nat.sub_self]; exact dvd_zero k⟩, heq, Nat.sub_self, Nat.zero_div]
    simp
  · have h1 : t ≤ n - 1 := by omega
    have hnt : n - t = (n - 1 - t) + 1 := by omega
    rw [if_pos h1, hnt, Nat.succ_div]
    by_cases hd : k ∣ n - 1 - t + 1
    · rw [if_pos ⟨htn, hd⟩, if_pos hd]; push_cast; ring
    · rw [if_neg (fun h => hd h.2), if_neg hd]; simp
