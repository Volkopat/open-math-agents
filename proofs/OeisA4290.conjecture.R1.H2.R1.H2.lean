import OMAReductions.R_OeisA4290_conjecture_R1_H2_R1

/-!
Step `OeisA4290.conjecture.R1.H2.R1.H2`: a repunit followed by `e` zeros.

Take `m = ofDigits 10 (replicate e 0 ++ replicate t 1)`, i.e. `10^e * R` with `R` the repunit
with `t` ones, so `9 R = 10^t - 1`. Its digits are `0` and `1`. Since `9 d ∣ 9 R`, `d ∣ R`, so
`n ∣ 10^e * d ∣ m`. Finally `9 m + 9 = 10^(t+e) - 10^e + 9 ≤ 10^(9k) - 1` because `t + e ≤ 9k`
and `10^e ≥ 10`, so `m < (10^(9k) - 1) / 9`.
-/

namespace OMA.OeisA4290H2

lemma ofDigits_replicate_zero (e : ℕ) : Nat.ofDigits 10 (List.replicate e 0) = 0 := by
  induction e with
  | zero => simp
  | succ e ih => simp [List.replicate_succ, Nat.ofDigits_cons, ih]

lemma nine_mul_repunit (t : ℕ) : 9 * Nat.ofDigits 10 (List.replicate t 1) = 10 ^ t - 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    have h1 : 1 ≤ 10 ^ t := Nat.one_le_pow _ _ (by norm_num)
    omega

lemma getLast_ne_zero (e t : ℕ) (ht : 0 < t) (h : List.replicate e 0 ++ List.replicate t 1 ≠ []) :
    (List.replicate e 0 ++ List.replicate t 1).getLast h ≠ 0 := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  first
  | simp [List.replicate_succ', ← List.append_assoc]
  | (rw [List.getLast_append_of_ne_nil (by simp)]; simp)
  | (simp only [List.replicate_succ', ← List.append_assoc, List.getLast_append_singleton]; norm_num)
  | (rw [List.getLast_append' _ _ (by simp)]; simp [List.getLast_replicate_succ])

end OMA.OeisA4290H2

open OMA.OeisA4290H2 in
theorem OMA.solution : OMA.R_OeisA4290_conjecture_R1_H2_R1.H2 := by
  intro k n d e t hn hlt he ht hnd hd hle
  have h9R := nine_mul_repunit t
  set R := Nat.ofDigits 10 (List.replicate t 1) with hR
  have hm : Nat.ofDigits 10 (List.replicate e 0 ++ List.replicate t 1) = 10 ^ e * R := by
    rw [Nat.ofDigits_append, ofDigits_replicate_zero, List.length_replicate, zero_add]
  have hP : 10 ≤ 10 ^ t := by
    calc (10 : ℕ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  have hQ : 10 ≤ 10 ^ e := by
    calc (10 : ℕ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hZ : 10 ^ e * 10 ^ t ≤ 10 ^ (9 * k) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hRpos : 1 ≤ R := by omega
  refine ⟨Nat.ofDigits 10 (List.replicate e 0 ++ List.replicate t 1), ?_, ?_, ?_, ?_⟩
  · rw [hm]
    apply Nat.lt_of_succ_le
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have h1 : 9 * (10 ^ e * R) = 10 ^ e * 10 ^ t - 10 ^ e := by
      rw [show 9 * (10 ^ e * R) = 10 ^ e * (9 * R) by ring, h9R, Nat.mul_sub_one]
    have hyQ : 10 ^ e ≤ 10 ^ e * 10 ^ t := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  · rw [hm]; positivity
  · rw [hm]
    have hdR : d ∣ R := by
      have h : 9 * d ∣ 9 * R := by rw [h9R]; exact hd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
    exact dvd_trans hnd (Nat.mul_dvd_mul_left _ hdR)
  · rw [Nat.digits_ofDigits 10 (by norm_num)]
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact Or.inl (List.eq_of_mem_replicate h)
      · exact Or.inr (List.eq_of_mem_replicate h)
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · rw [List.eq_of_mem_replicate h]; norm_num
      · rw [List.eq_of_mem_replicate h]; norm_num
    · intro hne
      exact getLast_ne_zero e t ht hne
