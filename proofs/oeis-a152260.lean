import OMAStatements.S_oeis_a152260
import Mathlib

namespace OMA.S_oeis_a152260
open PowerSeries

lemma stir_gt : ∀ n k, n < k → stirling2 n k = 0 := by
  intro n
  induction n with
  | zero => intro k hk; cases k with
    | zero => omega
    | succ k => simp [stirling2]
  | succ n ih => intro k hk; cases k with
    | zero => omega
    | succ k =>
      simp only [stirling2]
      rw [ih (k+1) (by omega), ih k (by omega)]; simp

lemma stir_succ_zero (n : ℕ) : stirling2 (n+1) 0 = 0 := by simp [stirling2]

lemma desc_step (j k : ℕ) : j * j.descFactorial k = j.descFactorial (k+1) + k * j.descFactorial k := by
  rcases le_or_gt k j with h | h
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.descFactorial_succ]
    simp only [Nat.add_sub_cancel_left]
    ring
  · have h1 : j.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h
    have h2 : j.descFactorial (k+1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h1, h2]

lemma pow_expand : ∀ n j : ℕ, j ^ n = ∑ k ∈ Finset.range (n+1), stirling2 n k * j.descFactorial k := by
  intro n
  induction n with
  | zero => intro j; simp [stirling2]
  | succ n ih =>
    intro j
    rw [pow_succ, ih j, Finset.sum_mul]
    have e1 : ∀ k ∈ Finset.range (n+1), stirling2 n k * j.descFactorial k * j =
        stirling2 n k * j.descFactorial (k+1) + k * stirling2 n k * j.descFactorial k := by
      intro k _
      have := desc_step j k
      calc _ = stirling2 n k * (j * j.descFactorial k) := by ring
        _ = _ := by rw [this]; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' _ (n+1), stir_succ_zero]
    simp only [stirling2, Nat.zero_mul, zero_mul, add_zero]
    have e2 : ∀ k ∈ Finset.range (n+1), ((k+1) * stirling2 n (k+1) + stirling2 n k) * j.descFactorial (k+1)
        = (k+1) * stirling2 n (k+1) * j.descFactorial (k+1) + stirling2 n k * j.descFactorial (k+1) := by
      intro k _; ring
    rw [Finset.sum_congr rfl e2, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun k => k * stirling2 n k * j.descFactorial k) n,
      Finset.sum_range_succ (fun k => (k+1) * stirling2 n (k+1) * j.descFactorial (k+1)) n,
      stir_gt n (n+1) (by omega)]
    simp only [Nat.cast_zero, zero_mul, add_zero, mul_zero]
    ring

lemma coeff_one_sub_pow (d i : ℕ) :
    coeff i ((1 - X : ℚ⟦X⟧) ^ d) = (-1) ^ i * (d.choose i : ℚ) := by
  have h : (1 - X : ℚ⟦X⟧) ^ d = rescale (-1 : ℚ) ((1 + X) ^ d) := by
    simp [sub_eq_add_neg]
  rw [h]
  have h2 : ((1 + X : ℚ⟦X⟧)) ^ d = ((((1 + Polynomial.X) ^ d : Polynomial ℚ)) : ℚ⟦X⟧) := by
    simp
  rw [h2, coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]


lemma choose_id (p k i : ℕ) :
    (p+k+i).choose (k+i) * (k+i).descFactorial k = (k.factorial * (p+k).choose k) * (p+k+i).choose i := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  have h1 : (p+k+i).choose (k+i) * (k+i).choose k = (p+k+i).choose k * (p+i).choose i := by
    have := Nat.choose_mul (n := p+k+i) (k := k+i) (s := k) (by omega)
    rw [this]
    have e1 : p+k+i-k = p+i := by omega
    have e2 : k+i-k = i := by omega
    rw [e1, e2]
  have h2 : (p+k).choose k * (p+k+i).choose i = (p+k+i).choose k * (p+i).choose i := by
    have := Nat.choose_mul (n := p+k+i) (k := p+k) (s := k) (by omega)
    have e1 : p+k+i-k = p+i := by omega
    have e2 : p+k-k = p := by omega
    rw [e1, e2] at this
    have h3 : (p+k+i).choose (p+k) = (p+k+i).choose i := Nat.choose_symm_add
    have h4 : (p+i).choose p = (p+i).choose i := Nat.choose_symm_add
    rw [h3, h4] at this
    rw [mul_comm]; exact this
  calc (p+k+i).choose (k+i) * (k.factorial * (k+i).choose k)
      = k.factorial * ((p+k+i).choose (k+i) * (k+i).choose k) := by ring
    _ = k.factorial * ((p+k).choose k * (p+k+i).choose i) := by rw [h1, h2]
    _ = _ := by ring

lemma hq (p k : ℕ) :
    (1 - X : ℚ⟦X⟧) ^ (p+k+1) * (mk fun i => ((p+k+i).choose (p+k) : ℚ)) = 1 := by
  have h := (invOneSubPow ℚ (p+k+1)).inv_val
  rw [invOneSubPow_inv_eq_one_sub_pow, invOneSubPow_val_succ_eq_mk_add_choose] at h
  exact h

lemma mkg_eq (p : ℕ) :
    (mk fun j => ((Nat.choose (p + 1 + j - 1) j : ℕ) : ℚ) * (j : ℚ) ^ (p+1)) =
    ∑ k ∈ Finset.range (p+2), C ((stirling2 (p+1) k : ℚ) * ((k.factorial * (p+k).choose k : ℕ) : ℚ)) *
      (X ^ k * mk fun i => ((p+k+i).choose (p+k) : ℚ)) := by
  ext j
  simp only [coeff_mk, map_sum, coeff_C_mul, coeff_X_pow_mul']
  have e : p + 1 + j - 1 = p + j := by omega
  rw [e]
  have hp : ((j ^ (p+1) : ℕ) : ℚ) = ∑ k ∈ Finset.range (p+2), (stirling2 (p+1) k : ℚ) * (j.descFactorial k : ℚ) := by
    rw [pow_expand (p+1) j]; push_cast; rfl
  rw [show ((j : ℚ) ^ (p+1)) = ((j ^ (p+1) : ℕ) : ℚ) by push_cast; rfl, hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k ≤ j
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
    simp only [if_pos hk, Nat.add_sub_cancel_left]
    have := choose_id p k i
    have h' : (((p+k+i).choose (k+i) * (k+i).descFactorial k : ℕ) : ℚ) =
        (((k.factorial * (p+k).choose k) * (p+k+i).choose i : ℕ) : ℚ) := by rw [this]
    have e3 : (p+k+i).choose (p+k) = (p+k+i).choose i := Nat.choose_symm_add
    rw [e3]
    push_cast at h' ⊢
    simp only [← add_assoc] at h' ⊢
    linear_combination (stirling2 (p+1) k : ℚ) * h'
  · have : j.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [hk, this]


lemma ser (p : ℕ) : a152260Series (p+1) =
    ∑ k ∈ Finset.range (p+2),
      C ((stirling2 (p+1) k : ℚ) * ((k.factorial * (p+k).choose k : ℕ) : ℚ) * (((p+1 : ℕ) : ℚ))⁻¹) *
        (X ^ k * (1 - X : ℚ⟦X⟧) ^ (p + 1 - k)) := by
  unfold a152260Series
  rw [mkg_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ p + 1 := by have := Finset.mem_range.mp hk; omega
  have hpow : (1 - X : ℚ⟦X⟧) ^ (2 * (p+1)) = (1 - X) ^ (p + 1 - k) * (1 - X) ^ (p + k + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]
  have h := hq p k
  simp only [map_mul]
  linear_combination (C (((p+1 : ℕ) : ℚ))⁻¹ * C ((stirling2 (p+1) k : ℚ)) * C (((k.factorial * (p+k).choose k : ℕ) : ℚ)) * X ^ k * (1 - X : ℚ⟦X⟧) ^ (p + 1 - k)) * h

lemma final (p m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ p + 1) :
    a152260 (p+1) m =
      ∑ k ∈ Finset.Icc 1 m,
        (Nat.choose (p + 1 + k) k : ℚ) * (Nat.choose (p + 1 - k) (m - k) : ℚ) *
          (Nat.factorial k : ℚ) * (-1 : ℚ) ^ (m - k) * (stirling2 (p+1) k : ℚ) /
          ((p + 1 + k : ℕ) : ℚ) := by
  unfold a152260
  rw [ser]
  simp only [map_sum, coeff_C_mul, coeff_X_pow_mul', coeff_one_sub_pow]
  symm
  rw [← Finset.sum_subset (s₁ := Finset.Icc 1 m) (s₂ := Finset.range (p+2))]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hk2 := (Finset.mem_Icc.mp hk).2
    rw [if_pos hk2]
    have h := Nat.choose_mul_succ_eq (p + k) k
    have e : p + k + 1 - k = p + 1 := by omega
    rw [e] at h
    have h' : ((p+k).choose k : ℚ) * ((p+k+1 : ℕ) : ℚ) = ((p+k+1).choose k : ℚ) * ((p+1 : ℕ) : ℚ) := by
      exact_mod_cast h
    have e2 : p + 1 + k = p + k + 1 := by omega
    rw [e2]
    have hp : ((p+1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hp2 : ((p+k+1 : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast at h' hp hp2 ⊢
    have key : ((p+k).choose k : ℚ) * ((p:ℚ)+1)⁻¹ = ((p+k+1).choose k : ℚ) * ((p:ℚ)+k+1)⁻¹ := by
      field_simp
      linear_combination h'
    linear_combination (-(stirling2 (p+1) k : ℚ) * (Nat.factorial k : ℚ) * (-1 : ℚ) ^ (m - k) * ((p + 1 - k).choose (m - k) : ℚ)) * key
  · intro k hk
    have := Finset.mem_Icc.mp hk
    have := Finset.mem_range.mpr (show k < p + 2 by omega)
    exact this
  · intro k hk hk2
    have hk3 := Finset.mem_range.mp hk
    by_cases h0 : k = 0
    · subst h0; simp [stir_succ_zero]
    · have : ¬ k ≤ m := fun h => hk2 (Finset.mem_Icc.mpr ⟨by omega, h⟩)
      simp [this]

end OMA.S_oeis_a152260

theorem OMA.solution : type_of% @OMA.S_oeis_a152260.main := by
  intro n m hn hm hmn
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  exact OMA.S_oeis_a152260.final p m hm hmn
