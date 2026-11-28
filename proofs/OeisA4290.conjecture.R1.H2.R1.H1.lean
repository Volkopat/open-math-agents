import OMAReductions.R_OeisA4290_conjecture_R1_H2_R1

/-!
Step `OeisA4290.conjecture.R1.H2.R1.H1`: digit stacking followed by `e` zeros.

Let `δ j = d / 10^j % 10` be the decimal digits of `d < 10^t`. Put `c i = [i / t + 1 ≤ δ (i % t)]`
and `M = ∑_{i < 9t} c i 10^i`: block `v` (positions `v t, ..., v t + t - 1`) holds the 0/1 number
`B v = ∑_j [v + 1 ≤ δ j] 10^j`, and `∑_v B v = d`. So `M = d + ∑_v (10^(v t) - 1) B v`, and
`10^t - 1 ∣ 10^(v t) - 1` gives `d ∣ M`. The digits of `M` and of `m = 10^e M` are `0` and `1`, and
`9 m + 9 ≤ 10^(e + 9t) - 10^e + 9 ≤ 10^(9k) - 1`.
-/

namespace OMA.OeisA4290H1

open Finset

lemma digits_add_zero_one (c : ℕ) (hc : c = 0 ∨ c = 1) (N : ℕ)
    (hN : ∀ x ∈ Nat.digits 10 N, x = 0 ∨ x = 1) :
    ∀ x ∈ Nat.digits 10 (c + 10 * N), x = 0 ∨ x = 1 := by
  by_cases h : c = 0 ∧ N = 0
  · obtain ⟨rfl, rfl⟩ := h; simp
  · have hne : c ≠ 0 ∨ N ≠ 0 := by tauto
    rw [Nat.digits_add 10 (by norm_num) c N (by omega) hne]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc
    · exact hN x hx

/-- A number `∑_{i<ℓ} c i 10^i` with 0/1 coefficients has only digits `0` and `1`. -/
lemma digits_sum_zero_one : ∀ (ℓ : ℕ) (c : ℕ → ℕ), (∀ i, c i = 0 ∨ c i = 1) →
    ∀ x ∈ Nat.digits 10 (∑ i ∈ range ℓ, c i * 10 ^ i), x = 0 ∨ x = 1 := by
  intro ℓ
  induction ℓ with
  | zero => intro c _; simp
  | succ ℓ ih =>
    intro c hc
    have hsplit : ∑ i ∈ range (ℓ + 1), c i * 10 ^ i
        = c 0 + 10 * ∑ i ∈ range ℓ, c (i + 1) * 10 ^ i := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_succ, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsplit]
    exact digits_add_zero_one (c 0) (hc 0) _ (ih (fun i => c (i + 1)) (fun i => hc (i + 1)))

lemma digits_ten_pow_mul : ∀ (e N : ℕ), (∀ x ∈ Nat.digits 10 N, x = 0 ∨ x = 1) →
    ∀ x ∈ Nat.digits 10 (10 ^ e * N), x = 0 ∨ x = 1 := by
  intro e
  induction e with
  | zero => intro N hN; simpa using hN
  | succ e ih =>
    intro N hN
    have h := digits_add_zero_one 0 (Or.inl rfl) (10 ^ e * N) (ih N hN)
    rwa [zero_add, ← mul_assoc, ← pow_succ'] at h

lemma nine_mul_geom (ℓ : ℕ) : 9 * ∑ i ∈ range ℓ, 10 ^ i = 10 ^ ℓ - 1 := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    have : 1 ≤ 10 ^ ℓ := Nat.one_le_pow _ _ (by norm_num)
    omega

lemma sum_digits_eq : ∀ (t d : ℕ), d < 10 ^ t → ∑ j ∈ range t, (d / 10 ^ j % 10) * 10 ^ j = d := by
  intro t
  induction t with
  | zero => intro d hd; simp at hd; simp [hd]
  | succ t ih =>
    intro d hd
    rw [Finset.sum_range_succ']
    have h1 : ∀ j ∈ range t, (d / 10 ^ (j + 1) % 10) * 10 ^ (j + 1)
        = 10 * ((d / 10) / 10 ^ j % 10 * 10 ^ j) := by
      intro j _
      rw [Nat.div_div_eq_div_mul, ← pow_succ', pow_succ]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ih (d / 10) (by
      rw [pow_succ] at hd; omega)]
    simp only [pow_zero, Nat.div_one, mul_one]
    omega

lemma sum_range_mul_split (f : ℕ → ℕ) (t : ℕ) : ∀ a : ℕ,
    ∑ i ∈ range (a * t), f i = ∑ v ∈ range a, ∑ j ∈ range t, f (v * t + j) := by
  intro a
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma count_le (δ : ℕ) (hδ : δ ≤ 9) :
    ∑ v ∈ range 9, (if v + 1 ≤ δ then 1 else 0) = δ := by
  interval_cases δ <;> decide

end OMA.OeisA4290H1

open OMA.OeisA4290H1 Finset in
set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_OeisA4290_conjecture_R1_H2_R1.H1 := by
  intro k n d e t hn hlt he ht hnd hd hle
  have hP10 : 10 ≤ 10 ^ t := by
    calc (10 : ℕ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      have := Nat.eq_zero_of_zero_dvd hd
      omega
    · exact h
  have hdlt : d < 10 ^ t := by
    have h1 : 0 < 10 ^ t - 1 := by omega
    have h2 := Nat.le_of_dvd h1 hd
    omega
  -- the stacked 0/1 number
  set c : ℕ → ℕ := fun i => if i / t + 1 ≤ d / 10 ^ (i % t) % 10 then 1 else 0 with hc
  have hc01 : ∀ i, c i = 0 ∨ c i = 1 := by
    intro i; simp only [hc]; split_ifs <;> simp
  set M : ℕ := ∑ i ∈ range (9 * t), c i * 10 ^ i with hM
  set B : ℕ → ℕ := fun v => ∑ j ∈ range t, (if v + 1 ≤ d / 10 ^ j % 10 then 1 else 0) * 10 ^ j
    with hB
  have hMB : M = ∑ v ∈ range 9, 10 ^ (v * t) * B v := by
    rw [hM, sum_range_mul_split _ t 9]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have h1 : (v * t + j) / t = v := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, zero_add]
    have h2 : (v * t + j) % t = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [hc, h1, h2, pow_add]
    ring
  have hBsum : ∑ v ∈ range 9, B v = d := by
    rw [hB, Finset.sum_comm]
    have : ∀ j ∈ range t, ∑ v ∈ range 9, (if v + 1 ≤ d / 10 ^ j % 10 then 1 else 0) * 10 ^ j
        = (d / 10 ^ j % 10) * 10 ^ j := by
      intro j _
      rw [← Finset.sum_mul, count_le _ (by omega)]
    rw [Finset.sum_congr rfl this, sum_digits_eq t d hdlt]
  have hMd : M = d + ∑ v ∈ range 9, (10 ^ (v * t) - 1) * B v := by
    rw [hMB, ← hBsum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    have : 1 ≤ 10 ^ (v * t) := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.sub_mul, one_mul]
    have : B v ≤ 10 ^ (v * t) * B v := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hdM : d ∣ M := by
    rw [hMd]
    refine dvd_add dvd_rfl (Finset.dvd_sum fun v _ => ?_)
    apply Dvd.dvd.mul_right
    have h := Nat.sub_one_dvd_pow_sub_one (10 ^ t) v
    rw [← pow_mul, mul_comm t v] at h
    exact dvd_trans hd h
  have hMpos : 0 < M := by rw [hMd]; omega
  have hM9 : 9 * M ≤ 10 ^ (9 * t) - 1 := by
    rw [← nine_mul_geom]
    apply Nat.mul_le_mul_left
    rw [hM]
    refine Finset.sum_le_sum fun i _ => ?_
    rcases hc01 i with h | h <;> rw [h] <;> simp
  refine ⟨10 ^ e * M, ?_, by positivity, ?_, ?_⟩
  · apply Nat.lt_of_succ_le
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have hQ : 10 ≤ 10 ^ e := by
      calc (10 : ℕ) = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have hZ : 10 ^ e * 10 ^ (9 * t) ≤ 10 ^ (9 * k) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 9 * (10 ^ e * M) ≤ 10 ^ e * 10 ^ (9 * t) - 10 ^ e := by
      calc 9 * (10 ^ e * M) = 10 ^ e * (9 * M) := by ring
        _ ≤ 10 ^ e * (10 ^ (9 * t) - 1) := Nat.mul_le_mul_left _ hM9
        _ = 10 ^ e * 10 ^ (9 * t) - 10 ^ e := by rw [Nat.mul_sub_one]
    have hyQ : 10 ^ e ≤ 10 ^ e * 10 ^ (9 * t) := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  · exact dvd_trans hnd (Nat.mul_dvd_mul_left _ hdM)
  · exact digits_ten_pow_mul e M (digits_sum_zero_one (9 * t) c hc01)
