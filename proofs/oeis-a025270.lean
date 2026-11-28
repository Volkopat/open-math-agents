import OMAStatements.S_oeis_a025270

/-! We record the initial conditions in a finite polynomial. Completing the square gives a
quadratic identity for the generating function. Its Euler derivative gives the recurrence. -/

namespace InitialConvolutionA025270


open Finset PowerSeries

private noncomputable abbrev XX : PowerSeries ℚ := X

private noncomputable def euler (f : PowerSeries ℚ) : PowerSeries ℚ := XX * derivative ℚ f

private theorem derivativeMul (f g : PowerSeries ℚ) :
    derivative ℚ (f * g) = f * derivative ℚ g + g * derivative ℚ f := by
  simpa only [smul_eq_mul] using (PowerSeries.derivative ℚ).leibniz f g

private theorem eulerMul (f g : PowerSeries ℚ) :
    euler (f * g) = f * euler g + g * euler f := by
  rw [euler, derivativeMul]
  simp only [euler]
  ring

private theorem eulerSub (f g : PowerSeries ℚ) :
    euler (f - g) = euler f - euler g := by simp [euler, mul_sub]

private theorem twoEuler (f : PowerSeries ℚ) : euler (2 * f) = 2 * euler f := by
  rw [eulerMul]
  have h : euler (2 : PowerSeries ℚ) = 0 := by
    rw [← map_ofNat (C (R := ℚ)) 2, euler, derivative_C, mul_zero]
  rw [h, mul_zero, add_zero]

private theorem squareEuler {S P : PowerSeries ℚ} (h : S ^ 2 = P) :
    2 * P * euler S = euler P * S := by
  have hd := congrArg euler h
  rw [pow_two, eulerMul S S] at hd
  linear_combination S * hd - 2 * euler S * h

private theorem coeffEuler (f : PowerSeries ℚ) (j : ℕ) :
    coeff j (euler f) = (j : ℚ) * coeff j f := by
  cases j with
  | zero => simp [euler]
  | succ j =>
    rw [euler, coeff_succ_X_mul, coeff_derivative]
    simp [mul_comm]

private noncomputable def term (a : ℚ) (j : ℕ) : PowerSeries ℚ := C a * XX ^ j

private theorem coeffTerm (a : ℚ) (j k : ℕ) :
    coeff k (term a j) = if k = j then a else 0 := coeff_C_mul_X_pow a j k

private theorem coeffTermMul (a : ℚ) (j k : ℕ) (f : PowerSeries ℚ) :
    coeff k (term a j * f) = a * (if j ≤ k then coeff (k - j) f else 0) := by
  rw [term, mul_assoc, coeff_C_mul, coeff_X_pow_mul']

private theorem conv (a : ℕ → ℚ) (t n : ℕ) :
    coeff n (PowerSeries.mk (fun k => if k = 0 then 0 else a k) *
        PowerSeries.mk (fun k => if k < t then 0 else a k)) =
      ∑ k ∈ range (n + 1), (if k = 0 then 0 else a k) * (if n - k < t then 0 else a (n - k)) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk]

private theorem convIcc (a : ℕ → ℚ) (t n : ℕ) (ht : t ≤ n) :
    (∑ k ∈ range (n + 1), (if k = 0 then 0 else a k) * (if n - k < t then 0 else a (n - k))) =
      ∑ k ∈ Icc 1 (n - t), a k * a (n - k) := by
  have sub : Icc 1 (n - t) ⊆ range (n + 1) := by
    intro k hk
    simp only [mem_Icc] at hk
    exact mem_range.mpr (by omega)
  rw [← sum_subset sub]
  · apply sum_congr rfl
    intro k hk
    simp only [mem_Icc] at hk
    rw [if_neg (by omega : k ≠ 0), if_neg (by omega : ¬n - k < t)]
  · intro k hkr hk
    have hkRange := mem_range.mp hkr
    simp only [mem_Icc] at hk
    by_cases e : k = 0
    · simp [e]
    · rw [if_pos (by omega : n - k < t), mul_zero]

set_option maxHeartbeats 2000000 in
theorem checked : type_of% @OMA.S_oeis_a025270.main := by
  intro a ha1 ha2 ha3 ha4 hrec n hn
  let F : PowerSeries ℚ := PowerSeries.mk (fun k => if k = 0 then 0 else a k)
  let G : PowerSeries ℚ := PowerSeries.mk (fun k => if k < 1 then 0 else a k)
  let B : PowerSeries ℚ := term (1) 0
  let P : PowerSeries ℚ := term (1) 1 + term (1) 2 + term (-3) 3 + term (-5) 4
  let D : PowerSeries ℚ := term (1) 0 + term (-4) 1 + term (-4) 2 + term (12) 3 + term (20) 4
  have hG : G = F - (B - 1) := by
    ext k
    simp only [G, F, B, map_sub, map_add, coeffTerm, coeff_mk, coeff_one]
    by_cases hk : k < 1
    · interval_cases k <;> norm_num [ha1, ha2, ha3, ha4]
    · have h0 : k ≠ 0 := by omega
      simp only [h0, hk, if_false]
      ring
  have hBase : F * G = F - P := by
    ext k
    change coeff k (PowerSeries.mk (fun t => if t = 0 then 0 else a t) *
      PowerSeries.mk (fun t => if t < 1 then 0 else a t)) = coeff k (F - P)
    rw [conv]
    simp only [F, P, map_sub, map_add, coeffTerm, coeff_mk, map_zero]
    by_cases hk : k < 5
    · interval_cases k <;> norm_num [Finset.sum_range_succ, ha1, ha2, ha3, ha4]
    · rw [convIcc a 1 k (by omega), ← hrec k (by omega)]
      simp only [if_neg (show k ≠ 0 by omega), if_false, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega, show k ≠ 4 by omega] <;> ring
  have hQuad : F ^ 2 - B * F + P = 0 := by
    rw [hG] at hBase
    linear_combination hBase
  have hDiscr : B ^ 2 - 4 * P = D := by
    simp only [B, P, D, term, map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hSquare : (B - 2 * F) ^ 2 = D := by
    linear_combination 4 * hQuad + hDiscr
  have hDerived := squareEuler hSquare
  rw [eulerSub, twoEuler] at hDerived
  have hEB : euler B = 0 := by
    simp only [B, euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hED : euler D = term (-4) 1 + term (-8) 2 + term (36) 3 + term (80) 4 := by
    simp only [D, euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  rw [hEB, hED] at hDerived
  have hDifferential : (term (1) 0 + term (-4) 1 + term (-4) 2 + term (12) 3 + term (20) 4) * euler F + (term (2) 1 + term (4) 2 + term (-18) 3 + term (-40) 4) * F = (term (1) 1 + term (2) 2 + term (-9) 3 + term (-20) 4) := by
    have hFour : (4 : PowerSeries ℚ) *
        ((term (1) 0 + term (-4) 1 + term (-4) 2 + term (12) 3 + term (20) 4) * euler F + (term (2) 1 + term (4) 2 + term (-18) 3 + term (-40) 4) * F - (term (1) 1 + term (2) 2 + term (-9) 3 + term (-20) 4)) = 0 := by
      simp only [B, D, term, map_ofNat, map_neg, map_one, map_zero] at hDerived ⊢
      linear_combination (-((1 : PowerSeries ℚ))) * hDerived
    have nonzero : (4 : PowerSeries ℚ) ≠ 0 := by
      intro hh
      have hc := congrArg (constantCoeff (R := ℚ)) hh
      simp only [map_ofNat, map_zero] at hc
      norm_num at hc
    exact sub_eq_zero.mp ((mul_eq_zero.mp hFour).resolve_left nonzero)
  have hCoeffs := congrArg (coeff n) hDifferential
  have hPred (i : ℕ) (hi : i ≤ 4) : i ≤ n := by omega
  have hNZ (i : ℕ) (hi : i ≤ 4) : n - i ≠ 0 := by omega
  have hIndex (i : ℕ) (hi : i ≤ 4) : ((n - i : ℕ) : ℚ) = (n : ℚ) - i :=
    Nat.cast_sub (hPred i hi)
  have hOther (i : ℕ) (hi : i ≤ 4) : n ≠ i := by omega
  simp only [add_mul, map_add, map_zero, coeffTermMul, coeffTerm, coeffEuler, F, coeff_mk,
    Nat.sub_zero, Nat.cast_ofNat, Nat.zero_le, if_true, if_false, hPred 0 (by decide), hPred 1 (by decide),
    hPred 2 (by decide), hPred 3 (by decide), hPred 4 (by decide), hNZ 0 (by decide), hNZ 1 (by decide),
    hNZ 2 (by decide), hNZ 3 (by decide), hNZ 4 (by decide), hIndex 0 (by decide), hIndex 1 (by decide),
    hIndex 2 (by decide), hIndex 3 (by decide), hIndex 4 (by decide), hOther 0 (by decide), hOther 1 (by decide),
    hOther 2 (by decide), hOther 3 (by decide), hOther 4 (by decide)] at hCoeffs
  linear_combination hCoeffs

end InitialConvolutionA025270

theorem OMA.solution : type_of% @OMA.S_oeis_a025270.main := InitialConvolutionA025270.checked
