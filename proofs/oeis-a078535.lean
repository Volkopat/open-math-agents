import OMAStatements.S_oeis_a078535
import Mathlib

namespace A078535Aux
open PowerSeries

lemma powPS_eq (a : ℕ → ℤ) : ∀ m k : ℕ, ((OMA.S_oeis_a078535.powPS a m k : ℤ) : ℚ)
    = coeff k ((PowerSeries.mk (fun k => (a k : ℚ))) ^ m) := by
  intro m
  induction m with
  | zero => intro k; cases k <;> simp [OMA.S_oeis_a078535.powPS, coeff_one]
  | succ m ih =>
    intro k
    rw [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [OMA.S_oeis_a078535.powPS, OMA.S_oeis_a078535.mulPS]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [ih, coeff_mk]

lemma K (A : ℚ⟦X⟧) (hA : constantCoeff A = 1) (e : ℕ) :
    coeff e ((A + X * derivative ℚ A) * A⁻¹ ^ (e + 1)) = if e = 0 then 1 else 0 := by
  have hAV : A * A⁻¹ = 1 := PowerSeries.mul_inv_cancel A (by rw [hA]; exact one_ne_zero)
  have h1 : (A + X * derivative ℚ A) * A⁻¹ ^ (e + 1)
      = A⁻¹ ^ e + X * (derivative ℚ A * A⁻¹ ^ (e + 1)) := by
    rw [pow_succ]
    linear_combination (A⁻¹ ^ e) * hAV
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [h1]; simp
  · obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
    rw [if_neg (by omega), h1]
    have h2 : derivative ℚ (A⁻¹ ^ (d + 1))
        = -(C ((d : ℚ) + 1)) * (derivative ℚ A * A⁻¹ ^ (d + 1 + 1)) := by
      rw [derivative_pow, derivative_inv']
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, map_add, map_one, map_natCast]
      ring
    have h3 := coeff_derivative (A⁻¹ ^ (d + 1)) d
    rw [h2, neg_mul, map_neg, coeff_C_mul] at h3
    rw [map_add, coeff_succ_X_mul]
    have hd : ((d : ℚ) + 1) ≠ 0 := by positivity
    have h5 : ((d : ℚ) + 1) * (coeff (d + 1) (A⁻¹ ^ (d + 1))
        + coeff d (derivative ℚ A * A⁻¹ ^ (d + 1 + 1))) = 0 := by linarith
    rcases mul_eq_zero.mp h5 with h | h
    · exact absurd h hd
    · exact h

lemma L1 (A : ℚ⟦X⟧) (hA : constantCoeff A = 1) (c : ℚ) (M k : ℕ) (hk : k ≤ M) :
    coeff M ((A + X * derivative ℚ A) * A⁻¹ ^ (M + 1) * (C c * X * A) ^ k)
      = if k = M then c ^ M else 0 := by
  have hVA : A⁻¹ * A = 1 := PowerSeries.inv_mul_cancel A (by rw [hA]; exact one_ne_zero)
  have hVAk : A⁻¹ ^ k * A ^ k = 1 := by rw [← mul_pow, hVA, one_pow]
  have h1 : (A + X * derivative ℚ A) * A⁻¹ ^ (M + 1) * (C c * X * A) ^ k
      = C (c ^ k) * (X ^ k * ((A + X * derivative ℚ A) * A⁻¹ ^ (M - k + 1))) := by
    have : M + 1 = (M - k + 1) + k := by omega
    rw [this, pow_add, mul_pow, mul_pow, map_pow]
    linear_combination ((A + X * derivative ℚ A) * A⁻¹ ^ (M - k + 1) * C c ^ k * X ^ k) * hVAk
  rw [h1, coeff_C_mul, coeff_X_pow_mul', if_pos hk, K A hA]
  by_cases h : k = M
  · subst h; simp
  · rw [if_neg (by omega), if_neg h, mul_zero]

lemma L2 (A : ℚ⟦X⟧) (c : ℚ) (M : ℕ) (H : ℚ⟦X⟧) :
    coeff M ((A + X * derivative ℚ A) * A⁻¹ ^ (M + 1) * ((C c * X * A) ^ (M + 1) * H)) = 0 := by
  have h1 : (A + X * derivative ℚ A) * A⁻¹ ^ (M + 1) * ((C c * X * A) ^ (M + 1) * H)
      = X ^ (M + 1) * ((A + X * derivative ℚ A) * A⁻¹ ^ (M + 1) * (C c ^ (M + 1) * A ^ (M + 1) * H)) := by
    rw [mul_pow, mul_pow]; ring
  rw [h1, coeff_X_pow_mul', if_neg (by omega)]

lemma Mlem (A : ℚ⟦X⟧) (hA : constantCoeff A = 1) (c : ℚ) (M : ℕ) (β : ℕ → ℚ) (H : ℚ⟦X⟧)
    (hexp : A ^ (M + 1) = ∑ k ∈ Finset.range (M + 1), C (β k) * (C c * X * A) ^ k
      + (C c * X * A) ^ (M + 1) * H) :
    ((M : ℚ) + 1) * coeff M A = β M * c ^ M := by
  have hVA : A⁻¹ * A = 1 := PowerSeries.inv_mul_cancel A (by rw [hA]; exact one_ne_zero)
  have hVAk : A⁻¹ ^ (M + 1) * A ^ (M + 1) = 1 := by rw [← mul_pow, hVA, one_pow]
  have h0 : A + X * derivative ℚ A
      = (A + X * derivative ℚ A) * A⁻¹ ^ (M + 1) * A ^ (M + 1) := by
    rw [mul_assoc, hVAk, mul_one]
  have hl : coeff M (A + X * derivative ℚ A) = ((M : ℚ) + 1) * coeff M A := by
    rw [map_add]
    cases M with
    | zero => simp
    | succ m => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring
  rw [← hl, h0, hexp, mul_add, Finset.mul_sum, map_add, map_sum, L2, add_zero]
  have : ∀ k ∈ Finset.range (M + 1),
      coeff M ((A + X * derivative ℚ A) * A⁻¹ ^ (M + 1) * (C (β k) * (C c * X * A) ^ k))
        = if k = M then β k * c ^ M else 0 := by
    intro k hk
    have hk' : k ≤ M := by simpa [Nat.lt_succ_iff] using hk
    have e : (A + X * derivative ℚ A) * A⁻¹ ^ (M + 1) * (C (β k) * (C c * X * A) ^ k)
        = C (β k) * ((A + X * derivative ℚ A) * A⁻¹ ^ (M + 1) * (C c * X * A) ^ k) := by ring
    rw [e, coeff_C_mul, L1 A hA c M k hk']
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.range (M + 1)) M, if_pos (by simp)]

lemma E1 (G T : ℚ⟦X⟧) (hG : G = 1 + T * G) (m : ℕ) :
    G = ∑ k ∈ Finset.range m, C (1 : ℚ) * T ^ k + T ^ m * G := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    simp only [map_one, one_mul] at ih ⊢
    linear_combination ih + T ^ m * hG

lemma E2 (G T : ℚ⟦X⟧) (hG : G = 1 + T * G) (m : ℕ) :
    G ^ 2 = ∑ k ∈ Finset.range m, C ((k : ℚ) + 1) * T ^ k + T ^ m * (C (m : ℚ) * G + G ^ 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_succ, map_add, map_one] at ih ⊢
    linear_combination ih + T ^ m * (C (m : ℚ) + G + 1) * hG

end A078535Aux

open A078535Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a078535.main := by
  intro n hn a ha0 hrec
  have hA : constantCoeff (PowerSeries.mk (fun k => (a k : ℚ))) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, ha0]; simp
  have hpow := powPS_eq a
  generalize hAdef : PowerSeries.mk (fun k => (a k : ℚ)) = A at hA hpow
  have hEq : A ^ n = 1 + (C ((n : ℚ) ^ 2) * X * A) * A ^ n := by
    ext k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hA]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h := hrec (j + 1) (by omega)
      rw [Nat.add_sub_cancel] at h
      have h' : ((OMA.S_oeis_a078535.powPS a n (j + 1) : ℤ) : ℚ)
          - (n : ℚ) ^ 2 * ((OMA.S_oeis_a078535.powPS a (n + 1) j : ℤ) : ℚ) = 0 := by
        exact_mod_cast h
      rw [hpow, hpow] at h'
      have e : (C ((n : ℚ) ^ 2) * X * A) * A ^ n = C ((n : ℚ) ^ 2) * (X * A ^ (n + 1)) := by ring
      rw [map_add, e, coeff_C_mul, coeff_succ_X_mul, coeff_one, if_neg (by omega)]
      linarith
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hcoef : ∀ k, coeff k A = (a k : ℚ) := by intro k; rw [← hAdef, coeff_mk]
  constructor
  · obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
    have h := Mlem A hA (((M + 1 : ℕ) : ℚ) ^ 2) M (fun _ => 1) (A ^ (M + 1))
      (E1 (A ^ (M + 1)) _ hEq (M + 1))
    rw [hcoef] at h
    have h2 : ((a M : ℤ) : ℚ) = (((M + 1 : ℕ) : ℤ) : ℚ) ^ (2 * (M + 1) - 3) := by
      have e : 2 * (M + 1) - 3 = 2 * M - 1 := by omega
      have e2 : 2 * M = (2 * M - 1) + 1 := by omega
      rw [e]
      push_cast at h ⊢
      have h3 : ((M : ℚ) + 1) * (a M : ℚ) = ((M : ℚ) + 1) * ((M : ℚ) + 1) ^ (2 * M - 1) := by
        rw [h, one_mul, ← pow_mul, ← pow_succ', ← e2]
      exact mul_left_cancel₀ (by positivity) h3
    rw [Nat.add_sub_cancel]
    exact_mod_cast h2
  · obtain ⟨M, hM⟩ : ∃ M, 2 * n = M + 1 := ⟨2 * n - 1, by omega⟩
    have hE := E2 (A ^ n) _ hEq (M + 1)
    rw [← pow_mul, mul_comm n 2, hM] at hE
    have h := Mlem A hA ((n : ℚ) ^ 2) M (fun k => (k : ℚ) + 1) _ hE
    rw [hcoef] at h
    have h3 : ((a M : ℤ) : ℚ) = ((n : ℚ) ^ 2) ^ M := by
      have : ((M : ℚ) + 1) ≠ 0 := by positivity
      exact mul_left_cancel₀ this h
    have e1 : 2 * n - 1 = M := by omega
    have e2 : 4 * n - 2 = 2 * M := by omega
    rw [e1, e2, pow_mul]
    exact_mod_cast h3
