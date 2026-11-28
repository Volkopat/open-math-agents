import OMAStatements.S_oeis_a176756
import Mathlib

namespace OMA.P176756

open OMA.S_oeis_a176756 PowerSeries

lemma aList_succ (m : ℕ) : ∃ y : ℤ, aList (m + 1) = aList m ++ [y] := by
  rcases m with _ | m
  · exact ⟨4, rfl⟩
  · exact ⟨_, rfl⟩

lemma aList_length (m : ℕ) : (aList m).length = m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    obtain ⟨y, hy⟩ := aList_succ m
    rw [hy, List.length_append, ih]
    rfl

lemma aList_getD (m : ℕ) : ∀ p : ℕ, p ≤ m → (aList m).getD p 0 = a p := by
  induction m with
  | zero =>
    intro p hp
    have hp0 : p = 0 := by omega
    subst hp0
    rfl
  | succ m ih =>
    intro p hp
    rcases Nat.lt_or_ge p (m + 1) with h | h
    · obtain ⟨y, hy⟩ := aList_succ m
      rw [hy, List.getD_append _ _ _ _ (by rw [aList_length]; exact h)]
      exact ih p (by omega)
    · have hp1 : p = m + 1 := by omega
      subst hp1
      rfl

lemma a_rec (m : ℕ) :
    a (m + 2) = (∑ p ∈ Finset.range (m + 2), a p * a (m + 1 - p)) + (0 * (m : ℤ) + -2) := by
  have h : aList (m + 2) = aList (m + 1) ++ [(∑ p ∈ Finset.range (m + 2),
      (aList (m + 1)).getD p 0 * (aList (m + 1)).getD (m + 1 - p) 0) - 2] := rfl
  have hs : ∑ p ∈ Finset.range (m + 2), (aList (m + 1)).getD p 0 * (aList (m + 1)).getD (m + 1 - p) 0
      = ∑ p ∈ Finset.range (m + 2), a p * a (m + 1 - p) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_range] at hp
    rw [aList_getD (m + 1) p (by omega), aList_getD (m + 1) (m + 1 - p) (by omega)]
  have ha : a (m + 2) = (aList (m + 2)).getD (m + 2) 0 := rfl
  rw [ha, h, List.getD_append_right _ _ _ _ (by rw [aList_length])]
  rw [aList_length, Nat.sub_self, hs, List.getD_cons_zero]
  ring

lemma a_zero : a 0 = 1 := rfl
lemma a_one : a 1 = 4 := rfl

lemma dOfNat (m : ℕ) [m.AtLeastTwo] : derivative ℚ (ofNat(m) : PowerSeries ℚ) = 0 := by
  rw [← Nat.cast_ofNat (R := PowerSeries ℚ)]
  exact Derivation.map_natCast _ _

/-- The first-order differential equation satisfied by a series of the form (P + Q sqrt(Δ)) / D. -/
lemma ode (S Δ D P Q G : PowerSeries ℚ) (hS : S ^ 2 = Δ) (hG : D * G = P + Q * S) :
    2 * Δ * Q * D * derivative ℚ G
      + (2 * Δ * Q * derivative ℚ D - (2 * Δ * derivative ℚ Q + Q * derivative ℚ Δ) * D) * G
    = 2 * Δ * Q * derivative ℚ P - (2 * Δ * derivative ℚ Q + Q * derivative ℚ Δ) * P := by
  have hS' := congrArg (derivative ℚ) hS
  have hG' := congrArg (derivative ℚ) hG
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hS' hG'
  push_cast at hS' hG'
  linear_combination (2 * Δ * Q) * hG' - (2 * Δ * derivative ℚ Q + Q * derivative ℚ Δ) * hG
    + (Q ^ 2 * S) * hS' - (2 * Q ^ 2 * derivative ℚ S) * hS

/-- The generating function. -/
noncomputable def G : PowerSeries ℚ := PowerSeries.mk (fun k => (a k : ℚ))

/-- The inhomogeneous part. -/
noncomputable def Phi : PowerSeries ℚ := PowerSeries.mk (fun k : ℕ => (0 : ℚ) * (k : ℚ) + -2)

lemma H1 : G = 1 + C (4 : ℚ) * X - X + X * G ^ 2 + X ^ 2 * Phi := by
  ext k
  rcases k with _ | _ | k
  · simp [G, Phi, a_zero]
  · have h2 : coeff 0 (G ^ 2) = 1 := by
      rw [pow_two, coeff_mul]
      simp [G, a_zero]
    have h3 : coeff 1 (X * G ^ 2) = 1 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, h2]
    have h4 : coeff 1 (X ^ 2 * Phi) = 0 := by
      rw [coeff_X_pow_mul', if_neg (by norm_num)]
    simp only [map_add, map_sub, h3, h4, coeff_one, coeff_C_mul, coeff_X]
    rw [G, coeff_mk, a_one]
    norm_num
  · have h2 : coeff (k + 1) (G ^ 2) = ∑ p ∈ Finset.range (k + 2), (a p : ℚ) * (a (k + 1 - p) : ℚ) := by
      rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [G]
    have h3 : coeff (k + 2) (X * G ^ 2) = ∑ p ∈ Finset.range (k + 2), (a p : ℚ) * (a (k + 1 - p) : ℚ) := by
      rw [show k + 2 = (k + 1) + 1 from rfl, coeff_succ_X_mul, h2]
    have h4 : coeff (k + 2) (X ^ 2 * Phi) = (0 : ℚ) * (k : ℚ) + -2 := by
      rw [coeff_X_pow_mul, Phi, coeff_mk]
    have h5 : coeff (k + 2) (1 : PowerSeries ℚ) = 0 := by
      rw [coeff_one, if_neg (by omega)]
    have h6 : coeff (k + 2) (X : PowerSeries ℚ) = 0 := by
      rw [coeff_X, if_neg (by omega)]
    simp only [map_add, map_sub, h3, h4, h5, h6, coeff_C_mul, mul_zero]
    rw [G, coeff_mk, a_rec k]
    push_cast
    ring

lemma H2 : (1 - X) ^ 2 * Phi = C (-2 : ℚ) + C (2 : ℚ) * X := by
  have e : (1 - X) ^ 2 * Phi = Phi - C (2 : ℚ) * (X * Phi) + X ^ 2 * Phi := by
    simp only [map_ofNat]
    ring
  rw [e]
  ext k
  rcases k with _ | _ | k
  · simp [Phi]
  · have h4 : coeff 1 (X ^ 2 * Phi) = 0 := by
      rw [coeff_X_pow_mul', if_neg (by norm_num)]
    have h3 : coeff 1 (X * Phi) = (-2 : ℚ) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, Phi, coeff_mk]
      norm_num
    simp only [map_add, map_sub, h3, h4, coeff_C_mul, coeff_C, coeff_X]
    rw [Phi, coeff_mk]
    norm_num
  · have h4 : coeff (k + 2) (X ^ 2 * Phi) = (0 : ℚ) * (k : ℚ) + -2 := by
      rw [coeff_X_pow_mul, Phi, coeff_mk]
    have h3 : coeff (k + 2) (X * Phi) = (0 : ℚ) * ((k : ℚ) + 1) + -2 := by
      rw [show k + 2 = (k + 1) + 1 from rfl, coeff_succ_X_mul, Phi, coeff_mk]
      push_cast
      ring
    have h5 : coeff (k + 2) (C (-2 : ℚ) : PowerSeries ℚ) = 0 := by
      rw [coeff_C, if_neg (by omega)]
    have h6 : coeff (k + 2) (X : PowerSeries ℚ) = 0 := by
      rw [coeff_X, if_neg (by omega)]
    simp only [map_add, map_sub, h3, h4, h5, h6, coeff_C_mul, mul_zero]
    rw [Phi, coeff_mk]
    push_cast
    ring

/-- The quadratic equation of the generating function. -/
lemma hE : (X - 2 * X ^ 2 + X ^ 3) * G ^ 2 + (-1 + 2 * X - X ^ 2) * G + (1 + X - 7 * X ^ 2 + 5 * X ^ 3) = 0 := by
  have h1 := H1
  have h2 := H2
  simp only [map_ofNat, map_neg, map_one, map_zero] at h1 h2
  linear_combination (-(1 - X) ^ 2) * h1 - (X ^ 2) * h2

/-- S = -(2 A G + B), a square root of the discriminant. -/
noncomputable def S : PowerSeries ℚ := -((2 * X - 4 * X ^ 2 + 2 * X ^ 3) * G + (-1 + 2 * X - X ^ 2))

lemma hS : S ^ 2 = 1 - 8 * X + 10 * X ^ 2 + 28 * X ^ 3 - 79 * X ^ 4 + 68 * X ^ 5 - 20 * X ^ 6 := by
  unfold S
  linear_combination (4 * (X - 2 * X ^ 2 + X ^ 3)) * hE

lemma hG : (2 * X - 4 * X ^ 2 + 2 * X ^ 3) * G = (1 - 2 * X + X ^ 2) + (-1) * S := by
  unfold S
  ring

lemma dD : derivative ℚ (2 * X - 4 * X ^ 2 + 2 * X ^ 3 : PowerSeries ℚ) = 2 - 8 * X + 6 * X ^ 2 := by
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dP : derivative ℚ (1 - 2 * X + X ^ 2 : PowerSeries ℚ) = -2 + 2 * X := by
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dDl : derivative ℚ (1 - 8 * X + 10 * X ^ 2 + 28 * X ^ 3 - 79 * X ^ 4 + 68 * X ^ 5 - 20 * X ^ 6 : PowerSeries ℚ) = -8 + 20 * X + 84 * X ^ 2 - 316 * X ^ 3 + 340 * X ^ 4 - 120 * X ^ 5 := by
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dQ : derivative ℚ (-1 : PowerSeries ℚ) = 0 := by
  simp

lemma hODE : (-4 * X + 40 * X ^ 2 - 108 * X ^ 3 + 500 * X ^ 5 - 1016 * X ^ 6 + 940 * X ^ 7 - 432 * X ^ 8 + 80 * X ^ 9) * derivative ℚ G + (-4 + 32 * X - 108 * X ^ 2 + 216 * X ^ 3 - 284 * X ^ 4 + 240 * X ^ 5 - 116 * X ^ 6 + 24 * X ^ 7) * G = -4 + 108 * X ^ 2 - 392 * X ^ 3 + 628 * X ^ 4 - 528 * X ^ 5 + 228 * X ^ 6 - 40 * X ^ 7 := by
  have h := ode S (1 - 8 * X + 10 * X ^ 2 + 28 * X ^ 3 - 79 * X ^ 4 + 68 * X ^ 5 - 20 * X ^ 6) (2 * X - 4 * X ^ 2 + 2 * X ^ 3) (1 - 2 * X + X ^ 2) (-1) G hS hG
  rw [dD, dP, dDl, dQ] at h
  linear_combination h

lemma hu : (4 - 16 * X + 24 * X ^ 2 - 16 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have h' := congrArg constantCoeff h
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero,
    constantCoeff_X] at h'
  norm_num at h'

lemma hT : (X - 6 * X ^ 2 - 3 * X ^ 3 + 28 * X ^ 4 - 20 * X ^ 5) * derivative ℚ G + (1 - 4 * X + 5 * X ^ 2 - 6 * X ^ 3) * G - (1 + 4 * X - 17 * X ^ 2 + 10 * X ^ 3) = 0 := by
  have h := hODE
  have hc : (X ^ 0 * (4 - 16 * X + 24 * X ^ 2 - 16 * X ^ 3 + 4 * X ^ 4) : PowerSeries ℚ) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hu
  have hm : (X ^ 0 * (4 - 16 * X + 24 * X ^ 2 - 16 * X ^ 3 + 4 * X ^ 4)) * ((X - 6 * X ^ 2 - 3 * X ^ 3 + 28 * X ^ 4 - 20 * X ^ 5) * derivative ℚ G + (1 - 4 * X + 5 * X ^ 2 - 6 * X ^ 3) * G - (1 + 4 * X - 17 * X ^ 2 + 10 * X ^ 3)) = 0 := by
    linear_combination (-1) * h
  exact (mul_eq_zero.mp hm).resolve_left hc

lemma hTC : C (1 : ℚ) * (X ^ 1 * derivative ℚ G) + C (-6 : ℚ) * (X ^ 2 * derivative ℚ G) + C (-3 : ℚ) * (X ^ 3 * derivative ℚ G) + C (28 : ℚ) * (X ^ 4 * derivative ℚ G) + C (-20 : ℚ) * (X ^ 5 * derivative ℚ G) + C (1 : ℚ) * (X ^ 0 * G) + C (-4 : ℚ) * (X ^ 1 * G) + C (5 : ℚ) * (X ^ 2 * G) + C (-6 : ℚ) * (X ^ 3 * G) - (C (1 : ℚ) * X ^ 0 + C (4 : ℚ) * X ^ 1 + C (-17 : ℚ) * X ^ 2 + C (10 : ℚ) * X ^ 3) = 0 := by
  have h := hT
  simp only [map_ofNat, map_neg, map_one, map_zero]
  linear_combination h

lemma hrec (N : ℕ) : (1 * ((N : ℚ) + 4) + (1)) * (a (N + 4) : ℚ) + (-6 * ((N : ℚ) + 4) + (2)) * (a (N + 3) : ℚ) + (-3 * ((N : ℚ) + 4) + (11)) * (a (N + 2) : ℚ) + (28 * ((N : ℚ) + 4) + (-90)) * (a (N + 1) : ℚ) + (-20 * ((N : ℚ) + 4) + (80)) * (a (N + 0) : ℚ) = 0 := by
  have h := congrArg (coeff (N + 4)) hTC
  have e1 : coeff (N + 4) (X ^ 1 * derivative ℚ G) = (a (N + 4) : ℚ) * ((N : ℚ) + 4) := by
    rw [show N + 4 = N + 3 + 1 from rfl, coeff_X_pow_mul, coeff_derivative, G, coeff_mk]
    push_cast
    ring
  have e2 : coeff (N + 4) (X ^ 2 * derivative ℚ G) = (a (N + 3) : ℚ) * ((N : ℚ) + 3) := by
    rw [show N + 4 = N + 2 + 2 from rfl, coeff_X_pow_mul, coeff_derivative, G, coeff_mk]
    push_cast
    ring
  have e3 : coeff (N + 4) (X ^ 3 * derivative ℚ G) = (a (N + 2) : ℚ) * ((N : ℚ) + 2) := by
    rw [show N + 4 = N + 1 + 3 from rfl, coeff_X_pow_mul, coeff_derivative, G, coeff_mk]
    push_cast
    ring
  have e4 : coeff (N + 4) (X ^ 4 * derivative ℚ G) = (a (N + 1) : ℚ) * ((N : ℚ) + 1) := by
    rw [show N + 4 = N + 0 + 4 from rfl, coeff_X_pow_mul, coeff_derivative, G, coeff_mk]
    push_cast
    ring
  have e5 : coeff (N + 4) (X ^ 5 * derivative ℚ G) = (a N : ℚ) * (N : ℚ) := by
    rcases N with _ | M
    · rw [coeff_X_pow_mul', if_neg (by omega)]
      simp
    · rw [show M + 1 + 4 = M + 5 from by omega, coeff_X_pow_mul, coeff_derivative, G, coeff_mk]
      push_cast
      ring
  have f0 : coeff (N + 4) (X ^ 0 * G) = (a (N + 4) : ℚ) := by
    rw [show N + 4 = N + 4 + 0 from rfl, coeff_X_pow_mul, G, coeff_mk]
  have f1 : coeff (N + 4) (X ^ 1 * G) = (a (N + 3) : ℚ) := by
    rw [show N + 4 = N + 3 + 1 from rfl, coeff_X_pow_mul, G, coeff_mk]
  have f2 : coeff (N + 4) (X ^ 2 * G) = (a (N + 2) : ℚ) := by
    rw [show N + 4 = N + 2 + 2 from rfl, coeff_X_pow_mul, G, coeff_mk]
  have f3 : coeff (N + 4) (X ^ 3 * G) = (a (N + 1) : ℚ) := by
    rw [show N + 4 = N + 1 + 3 from rfl, coeff_X_pow_mul, G, coeff_mk]
  have s0 : coeff (N + 4) (X ^ 0 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  have s1 : coeff (N + 4) (X ^ 1 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  have s2 : coeff (N + 4) (X ^ 2 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  have s3 : coeff (N + 4) (X ^ 3 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  simp only [map_add, map_sub, coeff_C_mul, e1, e2, e3, e4, e5, f0, f1, f2, f3, s0, s1, s2, s3, map_zero, mul_zero, sub_zero, add_zero] at h
  linear_combination h

end OMA.P176756

theorem OMA.solution : type_of% @OMA.S_oeis_a176756.main := by
  intro n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 4 := ⟨n - 4, by omega⟩
  have h := OMA.P176756.hrec N
  have t1 : N + 4 - 1 = N + 3 := by omega
  have t2 : N + 4 - 2 = N + 2 := by omega
  have t3 : N + 4 - 3 = N + 1 := by omega
  have t4 : N + 4 - 4 = N + 0 := by omega
  simp only [t1, t2, t3, t4]
  have hq : (((1 * ((N : ℤ) + 4) + (1)) * OMA.S_oeis_a176756.a (N + 4) + (-6 * ((N : ℤ) + 4) + (2)) * OMA.S_oeis_a176756.a (N + 3) + (-3 * ((N : ℤ) + 4) + (11)) * OMA.S_oeis_a176756.a (N + 2) + (28 * ((N : ℤ) + 4) + (-90)) * OMA.S_oeis_a176756.a (N + 1) + (-20 * ((N : ℤ) + 4) + (80)) * OMA.S_oeis_a176756.a (N + 0) : ℤ) : ℚ) = 0 := by
    push_cast
    linear_combination h
  have hz : (1 * ((N : ℤ) + 4) + (1)) * OMA.S_oeis_a176756.a (N + 4) + (-6 * ((N : ℤ) + 4) + (2)) * OMA.S_oeis_a176756.a (N + 3) + (-3 * ((N : ℤ) + 4) + (11)) * OMA.S_oeis_a176756.a (N + 2) + (28 * ((N : ℤ) + 4) + (-90)) * OMA.S_oeis_a176756.a (N + 1) + (-20 * ((N : ℤ) + 4) + (80)) * OMA.S_oeis_a176756.a (N + 0) = 0 := by
    exact_mod_cast hq
  push_cast
  linear_combination hz
