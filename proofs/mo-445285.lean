import OMAStatements.S_mo_445285

/-
Kurkov's identity R(n,k) = T(n,k) + R(n,k-1) through exponential generating functions over Q.
U = sum inv(j)/j! X^j and V = sum lc(m)/m! X^m satisfy U' = (1 + X) U and (1 - X) V' = X^2 V,
hence U * V = 1/(1 - X). With th = X d/dX one has th^[n] U = P n * U where P n = sum_i T n i X^i,
so R n k = coeff k (th^[n] U * V) = sum_{i <= k} T n i.
-/

open PowerSeries

namespace OMA.BC445285

open OMA.S_mo_445285

noncomputable def bcu (j : ℕ) : ℚ := (involutions j : ℚ) / (Nat.factorial j : ℚ)

noncomputable def bcv (m : ℕ) : ℚ := (longCycles m : ℚ) / (Nat.factorial m : ℚ)

noncomputable def bcU : PowerSeries ℚ := PowerSeries.mk bcu

noncomputable def bcV : PowerSeries ℚ := PowerSeries.mk bcv

noncomputable def bcP (n : ℕ) : PowerSeries ℚ := PowerSeries.mk fun i => (T n i : ℚ)

noncomputable def bth (f : PowerSeries ℚ) : PowerSeries ℚ := X * derivative ℚ f

theorem coeff_bcU (n : ℕ) : coeff n bcU = bcu n := coeff_mk n bcu

theorem coeff_bcV (n : ℕ) : coeff n bcV = bcv n := coeff_mk n bcv

theorem coeff_bcP (n i : ℕ) : coeff i (bcP n) = (T n i : ℚ) := coeff_mk i _

theorem u_rec (j : ℕ) : ((j : ℚ) + 1 + 1) * bcu (j + 1 + 1) = bcu (j + 1) + bcu j := by
  have hI0 : involutions (j + 1 + 1) = involutions (j + 1) + (j + 1) * involutions j := rfl
  have hI : (involutions (j + 1 + 1) : ℚ) =
      (involutions (j + 1) : ℚ) + ((j : ℚ) + 1) * (involutions j : ℚ) := by
    rw [hI0]
    push_cast <;> ring
  have hF1 : (Nat.factorial (j + 1) : ℚ) = ((j : ℚ) + 1) * (Nat.factorial j : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast <;> ring
  have hF2 : (Nat.factorial (j + 1 + 1) : ℚ) =
      ((j : ℚ) + 1 + 1) * (((j : ℚ) + 1) * (Nat.factorial j : ℚ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast <;> ring
  have hf : (Nat.factorial j : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hj1 : (j : ℚ) + 1 ≠ 0 := by positivity
  have hj2 : (j : ℚ) + 1 + 1 ≠ 0 := by positivity
  unfold bcu
  rw [hI, hF2, hF1]
  field_simp <;> ring

theorem v_rec (m : ℕ) :
    ((m : ℚ) + 1 + 1 + 1) * bcv (m + 1 + 1 + 1) = ((m : ℚ) + 1 + 1) * bcv (m + 1 + 1) + bcv m := by
  have hL0 : longCycles (m + 1 + 1 + 1) =
      (m + 2) * longCycles (m + 1 + 1) + (m + 2) * (m + 1) * longCycles m := rfl
  have hL : (longCycles (m + 1 + 1 + 1) : ℚ) =
      ((m : ℚ) + 2) * (longCycles (m + 1 + 1) : ℚ) +
        ((m : ℚ) + 2) * ((m : ℚ) + 1) * (longCycles m : ℚ) := by
    rw [hL0]
    push_cast <;> ring
  have hF3 : (Nat.factorial (m + 1 + 1 + 1) : ℚ) =
      ((m : ℚ) + 1 + 1 + 1) * (((m : ℚ) + 1 + 1) * (((m : ℚ) + 1) * (Nat.factorial m : ℚ))) := by
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast <;> ring
  have hF2 : (Nat.factorial (m + 1 + 1) : ℚ) =
      ((m : ℚ) + 1 + 1) * (((m : ℚ) + 1) * (Nat.factorial m : ℚ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast <;> ring
  have hf : (Nat.factorial m : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (m : ℚ) + 1 + 1 ≠ 0 := by positivity
  have h3 : (m : ℚ) + 1 + 1 + 1 ≠ 0 := by positivity
  unfold bcv
  rw [hL, hF3, hF2]
  field_simp <;> ring

theorem U_deriv : derivative ℚ bcU = (1 + X) * bcU := by
  ext n
  rw [coeff_derivative, add_mul, one_mul, map_add]
  rcases n with _ | m
  · rw [coeff_zero_X_mul, coeff_bcU, coeff_bcU]
    simp [bcu, involutions]
  · rw [coeff_succ_X_mul, coeff_bcU, coeff_bcU, coeff_bcU]
    have h := u_rec m
    push_cast
    linear_combination h

theorem V_deriv : (1 - X) * derivative ℚ bcV = X * (X * bcV) := by
  ext n
  rw [sub_mul, one_mul, map_sub]
  rcases n with _ | _ | m
  · rw [coeff_zero_X_mul, coeff_zero_X_mul, coeff_derivative, coeff_bcV]
    simp [bcv, longCycles]
  · rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_derivative, coeff_derivative,
      coeff_bcV, coeff_bcV]
    simp [bcv, longCycles]
  · rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative, coeff_derivative,
      coeff_bcV, coeff_bcV, coeff_bcV]
    have h := v_rec m
    push_cast
    linear_combination h

theorem D_deriv : derivative ℚ ((1 - X) * bcV) = -(1 + X) * ((1 - X) * bcV) := by
  rw [Derivation.leibniz]
  try simp only [smul_eq_mul]
  rw [V_deriv]
  have h1 : derivative ℚ (1 - X : PowerSeries ℚ) = -1 := by
    first
    | (rw [map_sub, derivative_X, Derivation.map_one_eq_zero]; ring)
    | (rw [Derivation.map_sub, derivative_X, Derivation.map_one_eq_zero]; ring)
    | simp
  rw [h1]
  ring

theorem cU : constantCoeff bcU = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_bcU]
  simp [bcu, involutions]

theorem cV : constantCoeff bcV = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_bcV]
  simp [bcv, longCycles]

theorem UD_one : bcU * ((1 - X) * bcV) = 1 := by
  refine derivative.ext ?_ ?_
  · rw [Derivation.leibniz, D_deriv, U_deriv, Derivation.map_one_eq_zero]
    try simp only [smul_eq_mul]
    ring
  · rw [map_mul, map_mul, map_sub, map_one, constantCoeff_X, cU, cV]
    norm_num

theorem W_eq (k : ℕ) : coeff k (bcU * bcV) = 1 := by
  have h : bcU * bcV - X * (bcU * bcV) = 1 := by linear_combination UD_one
  induction k with
  | zero =>
    have h0 := congrArg (coeff 0) h
    rw [map_sub, coeff_zero_X_mul, coeff_one, if_pos rfl, sub_zero] at h0
    exact h0
  | succ k ih =>
    have h1 := congrArg (coeff (k + 1)) h
    rw [map_sub, coeff_succ_X_mul, coeff_one, if_neg (show k + 1 ≠ 0 by omega), ih] at h1
    linarith

theorem coeff_bth (f : PowerSeries ℚ) (n : ℕ) : coeff n (bth f) = (n : ℚ) * coeff n f := by
  unfold bth
  rcases n with _ | m
  · rw [coeff_zero_X_mul]
    simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast <;> ring

theorem bth_mul (f g : PowerSeries ℚ) : bth (f * g) = bth f * g + f * bth g := by
  unfold bth
  rw [Derivation.leibniz]
  try simp only [smul_eq_mul]
  ring

theorem bth_U : bth bcU = (X + X ^ 2) * bcU := by
  unfold bth
  rw [U_deriv]
  ring

theorem P_zero : bcP 0 = 1 := by
  ext i
  rw [coeff_bcP, coeff_one]
  rcases i with _ | i
  · simp [T]
  · simp [T]

theorem P_succ (n : ℕ) : bth (bcP n) + (X + X ^ 2) * bcP n = bcP (n + 1) := by
  have e : (X + X ^ 2 : PowerSeries ℚ) * bcP n = X * bcP n + X * (X * bcP n) := by ring
  rw [e]
  ext i
  rw [map_add, map_add, coeff_bth]
  rcases i with _ | _ | k
  · rw [coeff_zero_X_mul, coeff_zero_X_mul, coeff_bcP, coeff_bcP]
    have h : T (n + 1) 0 = 0 := rfl
    rw [h]
    simp
  · rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_bcP, coeff_bcP, coeff_bcP]
    have h : T (n + 1) (0 + 1) = T n (0 + 1) + T n 0 := rfl
    rw [h]
    push_cast <;> ring
  · rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_bcP, coeff_bcP, coeff_bcP,
      coeff_bcP]
    have h : T (n + 1) (k + 1 + 1) = (k + 1 + 1) * T n (k + 1 + 1) + T n (k + 1) + T n k := rfl
    rw [h]
    push_cast <;> ring

theorem iter_U (n : ℕ) : bth^[n] bcU = bcP n * bcU := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, P_zero, one_mul]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, bth_mul, bth_U, ← P_succ n]
    ring

theorem coeff_iter (n k : ℕ) (f : PowerSeries ℚ) :
    coeff k (bth^[n] f) = (k : ℚ) ^ n * coeff k f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', coeff_bth, ih]
    ring

theorem R_eq (n k : ℕ) : R n k = coeff k (bth^[n] bcU * bcV) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold OMA.S_mo_445285.R
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by
    have := Finset.mem_range.mp hj
    omega
  try dsimp only
  rw [coeff_iter, coeff_bcU, coeff_bcV]
  unfold bcu bcv
  have hc : ((k.choose j : ℕ) : ℚ) * (j.factorial : ℚ) * ((k - j).factorial : ℚ) =
      (k.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjk
  have h1 : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have h2 : ((k - j).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - j)
  have h3 : ((k.choose j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjk).ne'
  rw [← hc]
  field_simp <;> ring

theorem R_sum (n k : ℕ) : R n k = ∑ i ∈ Finset.range (k + 1), (T n i : ℚ) := by
  rw [R_eq, iter_U, mul_assoc, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i _
  try dsimp only
  rw [coeff_bcP, W_eq, mul_one]

end OMA.BC445285

theorem OMA.solution : type_of% @OMA.S_mo_445285.main := by
  intro n k
  rw [OMA.BC445285.R_sum]
  rcases k with _ | k
  · simp
  · rw [if_neg (show k + 1 ≠ 0 by omega), show k + 1 - 1 = k by omega, OMA.BC445285.R_sum n k,
      Finset.sum_range_succ _ (k + 1)]
    ring
