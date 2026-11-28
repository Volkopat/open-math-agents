import OMAStatements.S_oeis_a355372

open PowerSeries Finset
open scoped PowerSeries

namespace OMA.A355372

private def geom (c : ℚ) : PowerSeries ℚ := mk fun n => c ^ n

private theorem geom_mul (c : ℚ) : (1 - C c * X) * geom c = 1 := by
  ext n
  cases n with
  | zero => simp [geom, sub_mul]
  | succ n =>
    simp [geom, sub_mul, mul_assoc, coeff_C_mul, coeff_succ_X_mul, pow_succ, mul_comm c]

private theorem geom_eq_inv (c : ℚ) : geom c = (1 - C c * X)⁻¹ := by
  have h : (1 - C c * X : PowerSeries ℚ) * (1 - C c * X)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  linear_combination (1 - C c * X)⁻¹ * geom_mul c - geom c * h

private theorem derivLogTimes {f : PowerSeries ℚ} (hf : constantCoeff f = 1) :
    (d⁄dX ℚ (logOf f)) * f = d⁄dX ℚ f := by
  have hs : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero' (by simp [hf])
  have hbase : (d⁄dX ℚ (log ℚ)) * (1 + X) = 1 := by
    rw [deriv_log]
    change geom (-1) * (1 + X) = 1
    simpa [mul_comm] using geom_mul (-1)
  have hsubst := congrArg (substAlgHom hs) hbase
  simp only [map_mul, map_add, map_one, substAlgHom_X, add_sub_cancel] at hsubst
  rw [logOf_eq, derivative_subst hs, map_sub, (derivative ℚ).map_one_eq_zero, sub_zero]
  rw [← coe_substAlgHom hs]
  calc
    _ = (substAlgHom hs (d⁄dX ℚ (log ℚ)) * f) * (d⁄dX ℚ f) := by ring
    _ = _ := by rw [hsubst, one_mul]

private theorem coeffLog (n : ℕ) :
    coeff n (logOf ((1 - X) * (1 - 2 * X)⁻¹ : PowerSeries ℚ)) =
      ((2 : ℚ) ^ n - 1) / n := by
  let u : PowerSeries ℚ := 1 - X
  let v : PowerSeries ℚ := 1 - 2 * X
  let f := u * v⁻¹
  have hu : u * u⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [u])
  have hv : v * v⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [v])
  have hcf : constantCoeff f = 1 := by simp [f, u, v, constantCoeff_inv]
  have hd := derivLogTimes hcf
  have htwo : (2 : PowerSeries ℚ) = C (2 : ℚ) := by
    rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]
    norm_num
  have hf' : (d⁄dX ℚ f) = -v⁻¹ + 2 * u * v⁻¹ ^ 2 := by
    dsimp only [f]
    rw [(derivative ℚ).leibniz, derivative_inv']
    have h₁ : (d⁄dX ℚ u) = -1 := by simp [u, (derivative ℚ).map_one_eq_zero]
    have h₂ : (d⁄dX ℚ v) = -2 := by
      simp [v, htwo, (derivative ℚ).leibniz, (derivative ℚ).map_one_eq_zero]
    simp only [h₁, h₂, smul_eq_mul]
    ring
  rw [hf'] at hd
  change (d⁄dX ℚ (logOf f)) * (u * v⁻¹) = _ at hd
  have hda : (d⁄dX ℚ (logOf f)) * u = -1 + 2 * u * v⁻¹ := by
    linear_combination v * hd - (1 + (d⁄dX ℚ (logOf f)) * u - 2 * u * v⁻¹) * hv
  have hd' : (d⁄dX ℚ (logOf f)) = 2 * v⁻¹ - u⁻¹ := by
    linear_combination u⁻¹ * hda - ((d⁄dX ℚ (logOf f)) - 2 * v⁻¹) * hu
  have hu' : u⁻¹ = geom 1 := by simpa [u, map_one] using (geom_eq_inv 1).symm
  have hv' : v⁻¹ = geom 2 := by simpa [v, ← htwo] using (geom_eq_inv 2).symm
  rw [hu', hv'] at hd'
  change coeff n (logOf f) = _
  cases n with
  | zero =>
    simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_logOf hcf]
  | succ n =>
    have h := congrArg (coeff n) hd'
    rw [coeff_derivative, map_sub] at h
    rw [htwo, coeff_C_mul] at h
    simp only [geom, coeff_mk, one_pow] at h
    rw [eq_div_iff (by positivity : ((n + 1 : ℕ) : ℚ) ≠ 0)]
    push_cast
    rw [pow_succ]
    linarith

private theorem denInv :
    ((1 - X : PowerSeries ℚ) ^ 3)⁻¹ = mk fun n => ((2 + n).choose 2 : ℚ) := by
  let f : PowerSeries ℚ := (1 - X) ^ 3
  let g : PowerSeries ℚ := mk fun n => ((2 + n).choose 2 : ℚ)
  have hg : g * f = 1 := mk_add_choose_mul_one_sub_pow_eq_one ℚ 2
  have hf : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [f])
  change f⁻¹ = g
  linear_combination g * hf - f⁻¹ * hg

private def term (p i : ℕ) : ℤ :=
  (p.factorial / i : ℕ) * ((2 : ℤ) ^ i - 1) * (2 + (p - i)).choose 2

private theorem coeffAsInt (p : ℕ) :
    OMA.S_oeis_a355372.a p = ((∑ i ∈ range (p + 1), term p i : ℤ) : ℚ) := by
  rw [OMA.S_oeis_a355372.a, OMA.S_oeis_a355372.egf, denInv, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum, Int.cast_sum]
  apply sum_congr rfl
  intro i hi
  simp only [coeffLog, coeff_mk, term, Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_pow,
    Int.cast_ofNat, Int.cast_one]
  by_cases h : i = 0
  · simp [h]
  · have hd := Nat.dvd_factorial (Nat.pos_of_ne_zero h)
        (show i ≤ p from Nat.le_of_lt_succ (mem_range.mp hi))
    rw [Nat.cast_div_charZero hd]
    ring

theorem solution : type_of% @OMA.S_oeis_a355372.main := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨∑ i ∈ range (p + 1), term p i, coeffAsInt p, ?_⟩
  apply (CharP.intCast_eq_zero_iff (ZMod p) p _).mp
  rw [Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_sum, sum_range_succ]
  have hsmall (i : ℕ) (hi : i ∈ range p) : (term p i : ZMod p) = 0 := by
    have hip := mem_range.mp hi
    by_cases hz : i = 0
    · simp [term, hz]
    · have hd : i ∣ p.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hz) hip.le
      have hpd : p ∣ p.factorial / i := by
        have hmul : p ∣ p.factorial / i * i := by
          rw [Nat.div_mul_cancel hd]
          exact hp.dvd_factorial.mpr le_rfl
        exact (hp.dvd_mul.mp hmul).resolve_right (fun hpi =>
          (not_le_of_gt hip) (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hpi))
      have hz' : (↑(p.factorial / i) : ZMod p) = 0 :=
        (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hpd
      simp only [term, Int.cast_mul, Int.cast_natCast, hz', zero_mul]
  rw [sum_eq_zero hsmall, zero_add]
  have hpdiv : p.factorial / p = (p - 1).factorial := by
    conv_lhs => rw [← Nat.sub_one_add_one_eq_of_pos hp.pos, Nat.factorial_succ]
    rw [Nat.sub_one_add_one_eq_of_pos hp.pos]
    simp [hp.pos, mul_comm p]
  simp only [term, hpdiv, Nat.sub_self, add_zero, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
    Int.cast_pow, Int.cast_ofNat, Int.cast_one]
  rw [ZMod.wilsons_lemma, ZMod.pow_card]
  norm_num

end OMA.A355372

theorem OMA.solution : type_of% @OMA.S_oeis_a355372.main := OMA.A355372.solution
