import OMAStatements.S_oeis_a370258
import Mathlib

namespace A370258P

open Finset

private noncomputable def ca : Polynomial ℚ := 1 + 3 * Polynomial.X
private noncomputable def cb : Polynomial ℚ := 2 * Polynomial.X + 3 * Polynomial.X ^ 2
private noncomputable def cc : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.X ^ 3

private noncomputable def Phi : Polynomial (Polynomial ℚ) :=
  1 + Polynomial.C ca * Polynomial.X + Polynomial.C cb * Polynomial.X ^ 2 +
    Polynomial.C cc * Polynomial.X ^ 3

private noncomputable def dPhi : Polynomial (Polynomial ℚ) :=
  Polynomial.C ca + Polynomial.C (2 * cb) * Polynomial.X +
    Polynomial.C (3 * cc) * Polynomial.X ^ 2

private lemma derivative_Phi : Polynomial.derivative Phi = dPhi := by
  rw [Phi, dPhi]
  simp only [map_add, map_mul, Polynomial.derivative_one, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_X_pow, Polynomial.derivative_mul, map_ofNat]
  push_cast
  rw [show (Polynomial.C (2 : Polynomial ℚ)) = 2 from map_ofNat _ 2,
    show (Polynomial.C (3 : Polynomial ℚ)) = 3 from map_ofNat _ 3]
  ring

private noncomputable def Y (s : ℕ) (q : Polynomial (Polynomial ℚ)) :
    PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk fun m => (q * Phi ^ (m + s)).coeff m

private lemma Y_add (s : ℕ) (q r : Polynomial (Polynomial ℚ)) : Y s (q + r) = Y s q + Y s r := by
  ext m; simp [Y, add_mul]

private lemma Y_C_mul (s : ℕ) (a : Polynomial ℚ) (q : Polynomial (Polynomial ℚ)) :
    Y s (Polynomial.C a * q) = PowerSeries.C a * Y s q := by
  ext m; simp [Y, mul_assoc, Polynomial.coeff_C_mul, PowerSeries.coeff_C_mul]

private lemma Y_X_mul (s : ℕ) (q : Polynomial (Polynomial ℚ)) :
    Y s (Polynomial.X * q) = PowerSeries.X * Y (s + 1) q := by
  ext m
  rcases m with _ | k
  · simp [Y, mul_assoc]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp only [Y, PowerSeries.coeff_mk, mul_assoc, Polynomial.coeff_X_mul]
    rw [show k + 1 + s = k + (s + 1) by ring]

private lemma Y_Phi_mul (s : ℕ) (q : Polynomial (Polynomial ℚ)) : Y s (Phi * q) = Y (s + 1) q := by
  ext m
  simp only [Y, PowerSeries.coeff_mk]
  rw [show q * Phi ^ (m + (s + 1)) = Phi * q * Phi ^ (m + s) by ring]

private lemma Y_X2 (s : ℕ) (q : Polynomial (Polynomial ℚ)) :
    Y s (Polynomial.X * (Polynomial.X * q)) =
      PowerSeries.X * (PowerSeries.X * Y (s + 2) q) := by
  rw [Y_X_mul, Y_X_mul]

private lemma Y_X3 (s : ℕ) (q : Polynomial (Polynomial ℚ)) :
    Y s (Polynomial.X * (Polynomial.X * (Polynomial.X * q))) =
      PowerSeries.X * (PowerSeries.X * (PowerSeries.X * Y (s + 3) q)) := by
  rw [Y_X_mul, Y_X2]

private def IsRec (F : ℕ → PowerSeries (Polynomial ℚ)) : Prop :=
  ∀ s, F (s + 1) = F s + PowerSeries.X * (PowerSeries.C ca * F (s + 1) +
    PowerSeries.X * (PowerSeries.C cb * F (s + 2) + PowerSeries.X * (PowerSeries.C cc * F (s + 3))))

private lemma Y_rec (q : Polynomial (Polynomial ℚ)) : IsRec (fun s => Y s q) := by
  intro s
  have h : Phi * q = q + Polynomial.C ca * (Polynomial.X * q) +
      Polynomial.C cb * (Polynomial.X * (Polynomial.X * q)) +
      Polynomial.C cc * (Polynomial.X * (Polynomial.X * (Polynomial.X * q))) := by
    rw [Phi]; ring
  have h2 := Y_Phi_mul s q
  rw [h, Y_add, Y_add, Y_add, Y_C_mul, Y_C_mul, Y_C_mul, Y_X_mul, Y_X2, Y_X3] at h2
  simp only
  linear_combination -h2

private lemma cXm (n : ℕ) (f : PowerSeries (Polynomial ℚ)) :
    PowerSeries.coeff n (PowerSeries.X * f) = if n = 0 then 0 else PowerSeries.coeff (n - 1) f := by
  rcases n with _ | n
  · simp
  · simp [PowerSeries.coeff_succ_X_mul]

private lemma rec_unique (F G : ℕ → PowerSeries (Polynomial ℚ)) (hF : IsRec F) (hG : IsRec G)
    (h0 : F 0 = G 0) : ∀ s, F s = G s := by
  have key : ∀ m s, PowerSeries.coeff m (F s) = PowerSeries.coeff m (G s) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro s
      induction s with
      | zero => rw [h0]
      | succ s ihs =>
        rw [hF, hG]
        simp only [map_add, cXm, PowerSeries.coeff_C_mul]
        rw [ihs]
        split_ifs with h1 h2 h3
        · rfl
        · rw [ih (m - 1) (by omega)]
        · rw [ih (m - 1) (by omega), ih (m - 1 - 1) (by omega)]
        · rw [ih (m - 1) (by omega), ih (m - 1 - 1) (by omega), ih (m - 1 - 1 - 1) (by omega)]
  intro s; exact PowerSeries.ext (fun m => key m s)

private lemma rec_mul (F : ℕ → PowerSeries (Polynomial ℚ)) (hF : IsRec F)
    (S : PowerSeries (Polynomial ℚ)) : IsRec (fun s => S * F s) := by
  intro s
  have h := hF s
  simp only
  linear_combination S * h

private lemma rec_shift (F : ℕ → PowerSeries (Polynomial ℚ)) (hF : IsRec F) :
    IsRec (fun s => F (s + 1)) := by
  intro s; exact hF (s + 1)

private noncomputable def Qs (s : ℕ) : PowerSeries (Polynomial ℚ) :=
  Y s 1 - PowerSeries.X * Y s dPhi

private lemma Qs_rec : IsRec Qs := by
  intro s
  have h1 := Y_rec 1 s
  have h2 := Y_rec dPhi s
  simp only at h1 h2
  simp only [Qs]
  linear_combination h1 - PowerSeries.X * h2

private lemma Qs_zero : Qs 0 = 1 := by
  refine PowerSeries.ext (fun m => ?_)
  rcases m with _ | k
  · simp [Qs, Y]
  · rw [Qs, map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one,
      if_neg (Nat.succ_ne_zero k)]
    simp only [Y, PowerSeries.coeff_mk, one_mul, add_zero]
    have hd := Polynomial.coeff_derivative (Phi ^ (k + 1)) k
    rw [Polynomial.derivative_pow_succ, derivative_Phi, mul_assoc,
      Polynomial.coeff_C_mul] at hd
    have hk : ((k : Polynomial ℚ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
    apply sub_eq_zero.mpr
    apply mul_left_cancel₀ hk
    rw [mul_comm dPhi (Phi ^ k)]
    linear_combination -hd

private noncomputable def Bser : PowerSeries (Polynomial ℚ) := Qs 1
private noncomputable def Gser : PowerSeries (Polynomial ℚ) := Y 0 1

private lemma Qs_pow (n : ℕ) : Qs n = Bser ^ n := by
  have hs : ∀ n, Qs (n + 1) = Qs 1 * Qs n := by
    have := rec_unique (fun n => Qs (n + 1)) (fun n => Qs 1 * Qs n) (rec_shift _ Qs_rec)
      (rec_mul _ Qs_rec _) (by simp [Qs_zero])
    exact this
  induction n with
  | zero => simp [Qs_zero]
  | succ n ih => rw [hs, ih, pow_succ, Bser, mul_comm]

private lemma B_eq : Bser = 1 + PowerSeries.X * (PowerSeries.C ca * Bser +
    PowerSeries.X * (PowerSeries.C cb * Bser ^ 2 + PowerSeries.X * (PowerSeries.C cc * Bser ^ 3))) := by
  have h := Qs_rec 0
  simp only [Qs_pow, zero_add, pow_one, pow_zero] at h
  exact h

private lemma Y_eq (s : ℕ) : Y s 1 = Gser * Bser ^ s := by
  have := rec_unique (fun s => Y s 1) (fun s => Gser * Qs s) (Y_rec 1)
    (rec_mul _ Qs_rec _) (by simp [Qs_zero, Gser])
  rw [this s, Qs_pow]

private lemma Y_dPhi (s : ℕ) : Y s dPhi = PowerSeries.C ca * Y s 1 +
    PowerSeries.C (2 * cb) * (PowerSeries.X * Y (s + 1) 1) +
    PowerSeries.C (3 * cc) * (PowerSeries.X * (PowerSeries.X * Y (s + 2) 1)) := by
  have h : dPhi = Polynomial.C ca * 1 + Polynomial.C (2 * cb) * (Polynomial.X * 1) +
      Polynomial.C (3 * cc) * (Polynomial.X * (Polynomial.X * 1)) := by
    rw [dPhi]; ring
  rw [h, Y_add, Y_add, Y_C_mul, Y_C_mul, Y_C_mul, Y_X_mul, Y_X2]

private lemma G_eq : Gser * (1 - PowerSeries.X * (PowerSeries.C ca +
    2 * PowerSeries.C cb * PowerSeries.X * Bser +
    3 * PowerSeries.C cc * PowerSeries.X ^ 2 * Bser ^ 2)) = 1 := by
  have h := Qs_zero
  rw [Qs, Y_dPhi, Y_eq, Y_eq, Y_eq] at h
  have e2 : PowerSeries.C (2 * cb) = 2 * (PowerSeries.C cb : PowerSeries (Polynomial ℚ)) := by
    rw [map_mul, map_ofNat]
  have e3 : PowerSeries.C (3 * cc) = 3 * (PowerSeries.C cc : PowerSeries (Polynomial ℚ)) := by
    rw [map_mul, map_ofNat]
  rw [e2, e3] at h
  linear_combination h

private noncomputable def th (f : PowerSeries (Polynomial ℚ)) : PowerSeries (Polynomial ℚ) :=
  PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) f

private lemma coeff_th (f : PowerSeries (Polynomial ℚ)) (m : ℕ) :
    PowerSeries.coeff m (th f) = (m : Polynomial ℚ) * PowerSeries.coeff m f := by
  rcases m with _ | k
  · simp [th]
  · rw [th, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]; push_cast; ring

private lemma th_mul (f g : PowerSeries (Polynomial ℚ)) : th (f * g) = th f * g + f * th g := by
  simp only [th, Derivation.leibniz, smul_eq_mul]; ring

private lemma th_add (f g : PowerSeries (Polynomial ℚ)) : th (f + g) = th f + th g := by
  simp only [th, map_add]; ring

private lemma th_X : th PowerSeries.X = PowerSeries.X := by simp [th]

private lemma th_one : th 1 = 0 := by simp [th]

private lemma th_C (a : Polynomial ℚ) : th (PowerSeries.C a) = 0 := by simp [th]

private lemma th_B : th Bser = (Gser - 1) * Bser := by
  have h1 : th Bser = (PowerSeries.C ca + 2 * PowerSeries.C cb * PowerSeries.X * Bser +
      3 * PowerSeries.C cc * PowerSeries.X ^ 2 * Bser ^ 2) *
      (PowerSeries.X * Bser + PowerSeries.X * th Bser) := by
    conv_lhs => rw [B_eq]
    simp only [th_add, th_mul, th_one, th_X, th_C, pow_succ, pow_zero, one_mul]
    ring
  have hG := G_eq
  linear_combination Gser * h1 - th Bser * hG - Bser * hG

/-! explicit coefficients -/

private lemma L_pow_coeff (M j : ℕ) :
    ((1 + Polynomial.C Polynomial.X * Polynomial.X : Polynomial (Polynomial ℚ)) ^ M).coeff j =
      Polynomial.C ((M.choose j : ℕ) : ℚ) * Polynomial.X ^ j := by
  induction M generalizing j with
  | zero =>
    rcases j with _ | j
    · simp
    · simp [Polynomial.coeff_one]
  | succ M ih =>
    rw [pow_succ, show ((1 + Polynomial.C Polynomial.X * Polynomial.X :
        Polynomial (Polynomial ℚ)) ^ M) * (1 + Polynomial.C Polynomial.X * Polynomial.X) =
        (1 + Polynomial.C Polynomial.X * Polynomial.X) ^ M + Polynomial.C Polynomial.X *
        (Polynomial.X * (1 + Polynomial.C Polynomial.X * Polynomial.X) ^ M) by ring]
    rcases j with _ | j
    · rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul_zero, ih]
      simp
    · rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, ih, ih,
        Nat.choose_succ_succ']
      push_cast
      simp only [map_add]
      ring

private lemma Phi_eq : Phi = (Polynomial.X + (1 + Polynomial.C Polynomial.X * Polynomial.X)) *
    (1 + Polynomial.C Polynomial.X * Polynomial.X) ^ 2 := by
  simp only [Phi, ca, cb, cc, map_add, map_mul, map_pow, map_one, map_ofNat]
  ring

private lemma Phi_pow_coeff (N m : ℕ) : (Phi ^ N).coeff m =
    ∑ i ∈ range (N + 1), ((N.choose i : ℕ) : Polynomial ℚ) *
      (if i ≤ m then Polynomial.C (((3 * N - i).choose (m - i) : ℕ) : ℚ) * Polynomial.X ^ (m - i)
        else 0) := by
  rw [Phi_eq, mul_pow, add_pow, Finset.sum_mul, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hiN : i ≤ N := by simp only [Finset.mem_range] at hi; omega
  have hp : (1 + Polynomial.C Polynomial.X * Polynomial.X : Polynomial (Polynomial ℚ)) ^ (N - i) *
      ((1 + Polynomial.C Polynomial.X * Polynomial.X) ^ 2) ^ N =
      (1 + Polynomial.C Polynomial.X * Polynomial.X) ^ (3 * N - i) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [show (Polynomial.X : Polynomial (Polynomial ℚ)) ^ i *
      (1 + Polynomial.C Polynomial.X * Polynomial.X) ^ (N - i) * ((N.choose i : ℕ) : Polynomial (Polynomial ℚ)) *
      ((1 + Polynomial.C Polynomial.X * Polynomial.X) ^ 2) ^ N =
      Polynomial.C ((N.choose i : ℕ) : Polynomial ℚ) * (Polynomial.X ^ i *
      ((1 + Polynomial.C Polynomial.X * Polynomial.X) ^ (N - i) *
      ((1 + Polynomial.C Polynomial.X * Polynomial.X) ^ 2) ^ N)) by
    rw [← Polynomial.C_eq_natCast]; ring]
  rw [hp, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs with h
  · rw [L_pow_coeff]
  · rfl

private lemma R_eq (n : ℕ) : (Phi ^ n).coeff n = OMA.S_oeis_a370258.R n := by
  rw [Phi_pow_coeff, OMA.S_oeis_a370258.R]
  refine Finset.sum_nbij' (fun x => n - x) (fun x => n - x) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_range] at ha; omega
  · intro a ha; simp only [Finset.mem_range] at ha; omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    have h1 : a ≤ n := by omega
    rw [if_pos h1, Nat.choose_symm h1, show 2 * n + (n - a) = 3 * n - a by omega]
    simp only [Nat.cast_mul, map_mul, map_natCast]
    ring

private lemma cancelC (m : ℕ) (x : ℚ) :
    ((m : Polynomial ℚ) + 1) * Polynomial.C (x / ((m + 1 : ℕ) : ℚ)) = Polynomial.C x := by
  rw [show ((m : Polynomial ℚ) + 1) = Polynomial.C ((m : ℚ) + 1) by simp, ← map_mul]
  congr 1
  have : ((m : ℚ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  push_cast
  field_simp

private lemma Icc_sum (n : ℕ) (f : ℕ → Polynomial ℚ) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

private lemma Bstmt_eq (m : ℕ) :
    (Phi ^ (m + 1)).coeff m = ((m : Polynomial ℚ) + 1) * OMA.S_oeis_a370258.B m := by
  have hB : OMA.S_oeis_a370258.B m = ∑ k ∈ Finset.Icc 1 (m + 1),
      Polynomial.C (OMA.S_oeis_a370258.T102537 (m + 1) k) * Polynomial.X ^ (k - 1) := by
    rcases m with _ | m
    · simp [OMA.S_oeis_a370258.B, OMA.S_oeis_a370258.T102537]
    · rw [OMA.S_oeis_a370258.B, if_neg (Nat.succ_ne_zero m)]
  rw [hB, Finset.mul_sum, Phi_pow_coeff, Finset.sum_range_succ,
    if_neg (by omega : ¬ (m + 1 ≤ m)), mul_zero, add_zero]
  refine Finset.sum_nbij' (fun x => m + 1 - x) (fun x => m + 1 - x) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_range, Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_range, Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_range] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    have h1 : a ≤ m := by omega
    rw [if_pos h1, OMA.S_oeis_a370258.T102537, ← mul_assoc ((m : Polynomial ℚ) + 1), cancelC,
      Nat.choose_symm (by omega : a ≤ m + 1),
      show 2 * (m + 1) + (m + 1 - a) = 3 * (m + 1) - a by omega,
      show m + 1 - a - 1 = m - a by omega]
    simp only [Nat.cast_mul, map_mul, map_natCast]
    ring

private lemma coeff_Bser (m : ℕ) : PowerSeries.coeff m Bser = OMA.S_oeis_a370258.B m := by
  have hk : ((m : Polynomial ℚ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  apply mul_left_cancel₀ hk
  rw [← Bstmt_eq]
  rcases m with _ | k
  · simp [Bser, Qs, Y]
  · rw [Bser, Qs, map_sub, PowerSeries.coeff_succ_X_mul]
    simp only [Y, PowerSeries.coeff_mk, one_mul]
    have hd := Polynomial.coeff_derivative (Phi ^ (k + 1 + 1)) k
    rw [Polynomial.derivative_pow_succ, derivative_Phi, mul_assoc,
      Polynomial.coeff_C_mul] at hd
    rw [show k + 1 + 1 = k + (1 + 1) by ring, show k + 1 = k + 1 by rfl] at hd ⊢
    rw [mul_comm dPhi]
    push_cast at hd ⊢
    linear_combination -hd

private lemma coeff_G1 (k : ℕ) :
    PowerSeries.coeff (k + 1) (Gser - 1) = OMA.S_oeis_a370258.R (k + 1) := by
  rw [map_sub, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero k), sub_zero, Gser]
  simp only [Y, PowerSeries.coeff_mk, one_mul, add_zero]
  exact R_eq (k + 1)

private lemma coeff_G1_zero : PowerSeries.coeff 0 (Gser - 1) = 0 := by
  simp [Gser, Y]

theorem main' (n : ℕ) (_hn : 1 ≤ n) : (n : Polynomial ℚ) * OMA.S_oeis_a370258.B n =
    ∑ j ∈ Finset.Icc 1 n, OMA.S_oeis_a370258.R j * OMA.S_oeis_a370258.B (n - j) := by
  have h := congrArg (PowerSeries.coeff n) th_B
  rw [coeff_th, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ'] at h
  simp only [coeff_Bser, coeff_G1, coeff_G1_zero, zero_mul, add_zero] at h
  rw [h, Icc_sum]

end A370258P

theorem OMA.solution : type_of% @OMA.S_oeis_a370258.main := by
  intro n hn
  exact A370258P.main' n hn
