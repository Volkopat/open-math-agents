import OMAStatements.S_oeis_a341309

namespace OMA.P_oeis_a341309

open OMA.S_oeis_a341309

theorem le_t_iff (n d : ℕ) : d ≤ t n ↔ d * (d + 1) ≤ 2 * n := by
  unfold t
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have hs : 1 ≤ Nat.sqrt (8 * n + 1) := Nat.le_sqrt.2 (by omega)
  have h1 : d * 2 ≤ Nat.sqrt (8 * n + 1) - 1 ↔ 2 * d + 1 ≤ Nat.sqrt (8 * n + 1) := by omega
  rw [h1, Nat.le_sqrt]
  have h2 : (2 * d + 1) * (2 * d + 1) = 4 * (d * (d + 1)) + 1 := by ring
  rw [h2]
  omega

theorem sum_consec (x j : ℕ) :
    ∑ i ∈ Finset.range (2 * j + 1), (x + i) = (2 * j + 1) * (x + j) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h := Finset.sum_range_id_mul_two (2 * j + 1)
  have h3 : (2 * j + 1) * (2 * j + 1 - 1) = ((2 * j + 1) * j) * 2 := by
    rw [show 2 * j + 1 - 1 = 2 * j by omega]
    ring
  rw [h3] at h
  have h4 : ∑ i ∈ Finset.range (2 * j + 1), i = (2 * j + 1) * j := by omega
  rw [h4]
  ring

theorem card_eq (n j : ℕ) :
    ((Finset.Icc 1 n).filter (fun x => ∑ i ∈ Finset.range (2 * j + 1), (x + i) = n)).card =
      if (2 * j + 1) ∣ n ∧ (2 * j + 1) * (2 * j + 1 + 1) ≤ 2 * n then 1 else 0 := by
  set k := 2 * j + 1 with hk
  have kpos : 0 < k := by omega
  have key : ∀ x, x ∈ (Finset.Icc 1 n).filter (fun x => ∑ i ∈ Finset.range k, (x + i) = n) ↔
      (k ∣ n ∧ k * (k + 1) ≤ 2 * n) ∧ x = n / k - j := by
    intro x
    simp only [Finset.mem_filter, Finset.mem_Icc, hk, sum_consec]
    rw [← hk]
    constructor
    · rintro ⟨⟨hx1, _⟩, hx⟩
      have hq : n / k = x + j := by
        rw [← hx]
        exact Nat.mul_div_cancel_left _ kpos
      refine ⟨⟨Dvd.intro _ hx, ?_⟩, by omega⟩
      rw [← hx, ← mul_assoc, mul_comm 2 k, mul_assoc]
      exact Nat.mul_le_mul_left k (by omega)
    · rintro ⟨⟨hdvd, hle⟩, rfl⟩
      obtain ⟨q, rfl⟩ := hdvd
      rw [Nat.mul_div_cancel_left _ kpos]
      have h1 : k * (k + 1) ≤ k * (2 * q) := hle.trans (le_of_eq (by ring))
      have h2 : k + 1 ≤ 2 * q := Nat.le_of_mul_le_mul_left h1 kpos
      have h3 : q ≤ k * q := Nat.le_mul_of_pos_left q kpos
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      congr 1
      omega
  split_ifs with hc
  · rw [Finset.card_eq_one]
    exact ⟨n / k - j, by ext x; rw [key, Finset.mem_singleton]; exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩⟩
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    exact hc ((key x).1 hx).1

end OMA.P_oeis_a341309

open OMA.S_oeis_a341309 OMA.P_oeis_a341309 in
theorem OMA.solution : type_of% @OMA.S_oeis_a341309.main := by
  intro n hn
  unfold a parts
  have hterm : ∀ k ∈ (Finset.range (n + 1)).filter Odd,
      k * ((Finset.Icc 1 n).filter (fun x => ∑ i ∈ Finset.range k, (x + i) = n)).card =
        if k ∣ n ∧ k * (k + 1) ≤ 2 * n then k else 0 := by
    intro k hk
    obtain ⟨j, rfl⟩ := (Finset.mem_filter.1 hk).2
    rw [card_eq]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_range, le_t_iff]
  constructor
  · rintro ⟨⟨hd, _⟩, hodd, hle⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hd), hodd, hd, hle⟩
  · rintro ⟨_, hodd, hd, hle⟩
    exact ⟨⟨hd, by omega⟩, hodd, hle⟩
