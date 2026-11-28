import OMAStatements.S_oeis_a372118

namespace OMA.P_oeis_a372118
open Finset OMA.S_oeis_a372118

def G (m N k : ℕ) : ℚ := ∑ i ∈ range (m + 1), (-1 : ℚ) ^ i * (m.choose i : ℚ) * ((k : ℚ) + m - i) ^ N

theorem G_rec (m N k : ℕ) : G (m + 1) (N + 1) k = ((k : ℚ) + m + 1) * G (m + 1) N k + (m + 1) * G m N k := by
  have h : G (m + 1) (N + 1) k - ((k : ℚ) + m + 1) * G (m + 1) N k
      = ∑ i ∈ range (m + 2), (-1 : ℚ) ^ i * ((m + 1).choose i : ℚ) * ((k : ℚ) + (m + 1 : ℕ) - i) ^ N * (-(i : ℚ)) := by
    unfold G
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    push_cast; ring
  have h2 : ∑ i ∈ range (m + 2), (-1 : ℚ) ^ i * ((m + 1).choose i : ℚ) * ((k : ℚ) + (m + 1 : ℕ) - i) ^ N * (-(i : ℚ))
      = (m + 1) * G m N k := by
    rw [sum_range_succ']
    unfold G
    rw [mul_sum]
    simp only [Nat.cast_zero, neg_zero, mul_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    have := Nat.add_one_mul_choose_eq m i
    have e : (((m + 1).choose (i + 1) : ℕ) : ℚ) * ((i : ℚ) + 1) = ((m : ℚ) + 1) * (m.choose i : ℚ) := by
      exact_mod_cast this.symm
    push_cast
    rw [pow_succ]
    linear_combination ((-1 : ℚ) ^ i * ((k : ℚ) + m - i) ^ N) * e
  linarith

theorem G_small (k : ℕ) : ∀ m : ℕ, (∀ N, N < m → G m N k = 0) ∧ G m m k = (m.factorial : ℚ) := by
  intro m
  induction m with
  | zero => simp [G]
  | succ m ih =>
    have z : ∀ N, N < m + 1 → G (m + 1) N k = 0 := by
      intro N
      induction N with
      | zero =>
        intro _
        have := Int.alternating_sum_range_choose (n := m + 1)
        simp only [G, pow_zero, mul_one]
        have h2 : (∑ i ∈ range (m + 2), ((-1 : ℤ) ^ i * ((m + 1).choose i : ℤ)) : ℤ) = 0 := by
          simpa using this
        exact_mod_cast congrArg (Int.cast : ℤ → ℚ) h2
      | succ N ihN =>
        intro hN
        rw [G_rec, ihN (by omega), ih.1 N (by omega)]; ring
    refine ⟨z, ?_⟩
    rw [G_rec, z m (by omega), ih.2, Nat.factorial_succ]; push_cast; ring

theorem fam_eq (m n k : ℕ) : fam m n k = G m (n + m) k / (m.factorial : ℚ) := rfl

theorem fam_zero (m k : ℕ) : fam m 0 k = 1 := by
  rw [fam_eq, zero_add, (G_small k m).2]
  exact div_self (by positivity)

theorem fam_rec (m n k : ℕ) :
    fam (m + 1) (n + 1) k = ((k : ℚ) + m + 1) * fam (m + 1) n k + fam m (n + 1) k := by
  rw [fam_eq, fam_eq, fam_eq, show n + 1 + (m + 1) = (n + (m + 1)) + 1 by ring, G_rec,
    show n + (m + 1) = n + 1 + m by ring, Nat.factorial_succ]
  have : (m.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp


theorem shift (f : ℕ → ℚ) (k : ℕ) (h0 : f 0 = 0) (hk : f (k + 1) = 0) :
    ∑ i ∈ range (k + 1), f i = ∑ i ∈ range (k + 1), f (i + 1) := by
  rw [sum_range_succ', sum_range_succ, h0, hk]

theorem kchoose (k i : ℕ) (hi : i ∈ range (k + 1)) :
    (k : ℚ) * (k.choose i : ℚ) = i * (k.choose i : ℚ) + (i + 1) * (k.choose (i + 1) : ℚ) := by
  have hi' : i ≤ k := by have := mem_range.mp hi; omega
  have := Nat.choose_succ_right_eq k i
  have e : ((k.choose (i + 1) : ℕ) : ℚ) * ((i : ℚ) + 1) = (k.choose i : ℚ) * ((k : ℚ) - i) := by
    rw [← Nat.cast_sub hi']; exact_mod_cast this
  linear_combination -e

theorem pw (k : ℕ) : ∀ n : ℕ, ∑ i ∈ range (k + 1),
    (Nat.stirlingSecond n i : ℚ) * (i.factorial : ℚ) * (k.choose i : ℚ) = (k : ℚ) ^ n := by
  intro n
  induction n with
  | zero =>
    rw [sum_range_succ']
    simp [Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    rw [pow_succ, ← ih, sum_mul]
    rw [shift (fun i => (Nat.stirlingSecond (n + 1) i : ℚ) * (i.factorial : ℚ) * (k.choose i : ℚ)) k
      (by simp [Nat.stirlingSecond_succ_zero]) (by simp)]
    have key := shift (fun i => (Nat.stirlingSecond n i : ℚ) * (i.factorial : ℚ) * i * (k.choose i : ℚ)) k
      (by simp) (by simp)
    have : ∑ i ∈ range (k + 1), (Nat.stirlingSecond n i : ℚ) * (i.factorial : ℚ) * (k.choose i : ℚ) * k
        = ∑ i ∈ range (k + 1), ((Nat.stirlingSecond n i : ℚ) * (i.factorial : ℚ) * i * (k.choose i : ℚ)
          + (Nat.stirlingSecond n i : ℚ) * ((i + 1).factorial : ℚ) * (k.choose (i + 1) : ℚ)) := by
      refine sum_congr rfl fun i hi => ?_
      have := kchoose k i hi
      rw [Nat.factorial_succ]; push_cast
      linear_combination ((Nat.stirlingSecond n i : ℚ) * (i.factorial : ℚ)) * this
    rw [this, sum_add_distrib, key, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [Nat.stirlingSecond_succ_succ]
    push_cast
    ring

def R (m n k : ℕ) : ℚ := ∑ i ∈ range (k + 1),
      (Nat.stirlingSecond (n + m) (i + m) : ℚ) * ((i + m).factorial : ℚ) / (m.factorial : ℚ)
        * (k.choose i : ℚ)

theorem R_rec (m n k : ℕ) :
    R (m + 1) (n + 1) k = ((k : ℚ) + m + 1) * R (m + 1) n k + R m (n + 1) k := by
  have key := shift (fun i => (Nat.stirlingSecond (n + m + 1) (i + m) : ℚ) * ((i + m).factorial : ℚ) * i
      / ((m + 1).factorial : ℚ) * (k.choose i : ℚ)) k (by simp) (by simp)
  have hm : (m.factorial : ℚ) ≠ 0 := by positivity
  have h : R (m + 1) (n + 1) k - ((k : ℚ) + m + 1) * R (m + 1) n k - R m (n + 1) k
      = ∑ i ∈ range (k + 1), ((Nat.stirlingSecond (n + m + 1) (i + m) : ℚ) * ((i + m).factorial : ℚ) * i
      / ((m + 1).factorial : ℚ) * (k.choose i : ℚ)) - ∑ i ∈ range (k + 1),
      ((Nat.stirlingSecond (n + m + 1) (i + 1 + m) : ℚ) * ((i + 1 + m).factorial : ℚ) * ((i + 1 : ℕ) : ℚ)
      / ((m + 1).factorial : ℚ) * (k.choose (i + 1) : ℚ)) := by
    unfold R
    rw [mul_sum, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i hi => ?_
    have e1 : n + 1 + (m + 1) = (n + m + 1) + 1 := by ring
    have e2 : i + (m + 1) = (i + m) + 1 := by ring
    have e3 : n + (m + 1) = n + m + 1 := by ring
    have e4 : n + 1 + m = n + m + 1 := by ring
    have e5 : i + 1 + m = (i + m) + 1 := by ring
    rw [e1, e2, e3, e4, e5, Nat.stirlingSecond_succ_succ, Nat.factorial_succ (i + m), Nat.factorial_succ m]
    have := kchoose k i hi
    push_cast
    field_simp
    linear_combination (-(Nat.stirlingSecond (n + m + 1) (i + m + 1) : ℚ) * ((i : ℚ) + m + 1)) * this
  rw [key] at h
  linarith

theorem fam_eq_R : ∀ m n k : ℕ, fam m n k = R m n k := by
  intro m
  induction m with
  | zero =>
    intro n k
    have := pw k n
    simp only [fam, R]
    simpa using this.symm
  | succ m ihm =>
    intro n
    induction n with
    | zero =>
      intro k
      rw [fam_zero, R, sum_range_succ']
      have : ∀ i, Nat.stirlingSecond (m + 1) (i + 1 + (m + 1)) = 0 :=
        fun i => Nat.stirlingSecond_eq_zero_of_lt (by omega)
      have hm : ((m + 1).factorial : ℚ) ≠ 0 := by positivity
      simp [this, Nat.stirlingSecond_self, hm]
    | succ n ihn =>
      intro k
      rw [fam_rec, R_rec, ihn, ihm]


theorem ogf_mul (m k : ℕ) : PowerSeries.mk (fun n => fam m n k) *
      (∏ i ∈ Icc k (k + m), (1 - PowerSeries.C (i : ℚ) * PowerSeries.X)) = 1 := by
  induction m with
  | zero =>
    ext n
    cases n with
    | zero => simp [fam]
    | succ n =>
      simp only [add_zero, Icc_self, prod_singleton, mul_sub, mul_one, map_sub,
        PowerSeries.coeff_mk, ← mul_assoc, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
      simp [fam, pow_succ]
  | succ m ih =>
    rw [← add_assoc, prod_Icc_succ_top (by omega), ← mul_assoc, mul_right_comm]
    have : PowerSeries.mk (fun n => fam (m + 1) n k) *
        (1 - PowerSeries.C ((k + m + 1 : ℕ) : ℚ) * PowerSeries.X) = PowerSeries.mk (fun n => fam m n k) := by
      ext n
      cases n with
      | zero => simp [fam_zero]
      | succ n =>
        simp only [mul_sub, mul_one, map_sub,
          PowerSeries.coeff_mk, ← mul_assoc, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
        rw [fam_rec]; push_cast; ring
    rw [this, ih]

theorem ogf (m k : ℕ) : PowerSeries.mk (fun n => fam m n k) =
      (∏ i ∈ Icc k (k + m), (1 - PowerSeries.C (i : ℚ) * PowerSeries.X))⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · exact ogf_mul m k
  · simp [map_prod]

theorem egf (m n : ℕ) : PowerSeries.mk (fun k => fam m n k / (k.factorial : ℚ)) =
      PowerSeries.exp ℚ * ∑ k ∈ range (n + 1),
        PowerSeries.C (((k + m).choose m : ℚ) * (Nat.stirlingSecond (n + m) (k + m) : ℚ))
          * PowerSeries.X ^ k := by
  have hp : (∑ k ∈ range (n + 1),
        PowerSeries.C (((k + m).choose m : ℚ) * (Nat.stirlingSecond (n + m) (k + m) : ℚ))
          * PowerSeries.X ^ k : PowerSeries ℚ)
      = PowerSeries.mk (fun k => ((k + m).choose m : ℚ) * (Nat.stirlingSecond (n + m) (k + m) : ℚ)) := by
    ext j
    simp only [map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_mk]
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range]
    split_ifs with h
    · rfl
    · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]; simp
  rw [hp]
  ext k
  rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, PowerSeries.coeff_mk,
    fam_eq_R, R, sum_div]
  rw [← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := by have := mem_range.mp hi; omega
  simp only [PowerSeries.coeff_exp, PowerSeries.coeff_mk, Nat.add_sub_cancel]
  have e1 : k - (k - i) = i := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.sub_le k i)
  rw [e1] at h1
  generalize k - i = j at *
  have h2 := Nat.add_choose_mul_factorial_mul_factorial j m
  have h1' : (k.choose j : ℚ) * j.factorial * i.factorial = k.factorial := by exact_mod_cast h1
  have h2' : ((j + m).choose m : ℚ) * j.factorial * m.factorial = (j + m).factorial := by
    rw [Nat.add_comm j m, Nat.choose_symm_add] at *
    exact_mod_cast h2
  have a1 : (i.factorial : ℚ) ≠ 0 := by positivity
  have a2 : (m.factorial : ℚ) ≠ 0 := by positivity
  have a3 : (j.factorial : ℚ) ≠ 0 := by positivity
  have a4 : (k.choose j : ℚ) ≠ 0 := by
    intro h
    have h0 : (k.factorial : ℚ) = 0 := by rw [← h1', h]; ring
    exact (Nat.cast_ne_zero.mpr k.factorial_ne_zero) h0
  rw [← h1', ← h2']
  simp only [map_div₀, map_one, eq_ratCast, Rat.cast_natCast, Algebra.algebraMap_self, RingHom.id_apply]
  field_simp

theorem A_eq (n k : ℕ) : A n k = fam 2 n k := by
  simp [A, fam, sum_range_succ]
  ring

end OMA.P_oeis_a372118

open Finset OMA.S_oeis_a372118 OMA.P_oeis_a372118 in
theorem OMA.solution : type_of% @OMA.S_oeis_a372118.main := by
  refine ⟨ogf, egf, fun m n k => fam_eq_R m n k, ?_, ?_, ?_⟩
  · intro k
    simp only [A_eq]; exact ogf 2 k
  · intro n
    simp only [A_eq]; exact egf 2 n
  · intro n k
    rw [A_eq, fam_eq_R, R]; norm_num

