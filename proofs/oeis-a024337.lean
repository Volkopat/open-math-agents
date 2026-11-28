import OMAStatements.S_oeis_a024337

-- Problem: A024337: Expansion of sinh(log(1+x))*log(1+x)/2
-- Credit: @neutroxium

namespace OMA.Proof_oeis_a024337

open OMA.S_oeis_a024337
open PowerSeries

private noncomputable def geomNeg : PowerSeries ℚ :=
  PowerSeries.mk fun n => (-1 : ℚ) ^ n

private lemma geomNeg_mul_one_add_X : geomNeg * (1 + X) = 1 := by
  ext n
  cases n with
  | zero =>
    simp [geomNeg, mul_add]
  | succ n =>
    rw [mul_add, mul_one, map_add, PowerSeries.coeff_succ_mul_X]
    simp [geomNeg, pow_succ]

private lemma deriv_log_eq_geomNeg : d⁄dX ℚ (PowerSeries.log ℚ) = geomNeg := by
  simpa [geomNeg] using (PowerSeries.deriv_log (A := ℚ))

private lemma constantCoeff_subst_zero_arg {a f : PowerSeries ℚ} (ha0 : constantCoeff a = 0) :
    constantCoeff (f.subst a) = constantCoeff f := by
  have ha : HasSubst a := HasSubst.of_constantCoeff_zero' ha0
  rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' ha,
    ← coeff_zero_eq_constantCoeff_apply]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    have h0 : coeff 0 (a ^ d) = 0 := by
      rw [coeff_zero_eq_constantCoeff, map_pow, ha0, zero_pow hd]
    simp [h0]

private lemma deriv_geomNeg : d⁄dX ℚ geomNeg = -(geomNeg * geomNeg) := by
  have h := congrArg (d⁄dX ℚ) geomNeg_mul_one_add_X
  rw [Derivation.map_one_eq_zero, Derivation.leibniz, map_add, Derivation.map_one_eq_zero,
    PowerSeries.derivative_X, zero_add] at h
  have hmul := congrArg (· * geomNeg) h
  simp only [zero_mul, add_mul, smul_eq_mul] at hmul
  have ha : (1 + X : PowerSeries ℚ) * geomNeg = 1 := by
    rw [mul_comm]; exact geomNeg_mul_one_add_X
  calc d⁄dX ℚ geomNeg
      = d⁄dX ℚ geomNeg * ((1 + X) * geomNeg) := by rw [ha, mul_one]
    _ = (1 + X) * d⁄dX ℚ geomNeg * geomNeg := by ring
    _ = -(geomNeg * 1 * geomNeg) := by
        have : (1 + X) * d⁄dX ℚ geomNeg * geomNeg + geomNeg * 1 * geomNeg = 0 := by
          linear_combination hmul
        exact eq_neg_of_add_eq_zero_left this
    _ = -(geomNeg * geomNeg) := by ring

private lemma exp_subst_log : (PowerSeries.exp ℚ).subst (PowerSeries.log ℚ) = 1 + X := by
  have hlog : HasSubst (PowerSeries.log ℚ) := HasSubst.log
  have hprod : (PowerSeries.exp ℚ).subst (PowerSeries.log ℚ) * geomNeg = 1 := by
    apply PowerSeries.derivative.ext
    · rw [Derivation.map_one_eq_zero, Derivation.leibniz, PowerSeries.derivative_subst hlog,
        PowerSeries.derivative_exp, deriv_log_eq_geomNeg, deriv_geomNeg]
      simp only [smul_eq_mul]
      ring
    · rw [map_mul, map_one, constantCoeff_subst_zero_arg PowerSeries.constantCoeff_log,
        PowerSeries.constantCoeff_exp]
      have h2 : constantCoeff geomNeg = 1 := by
        rw [← coeff_zero_eq_constantCoeff_apply]; simp [geomNeg]
      rw [h2, mul_one]
  calc (PowerSeries.exp ℚ).subst (PowerSeries.log ℚ)
      = ((PowerSeries.exp ℚ).subst (PowerSeries.log ℚ) * geomNeg) * (1 + X) := by
        rw [mul_assoc, geomNeg_mul_one_add_X, mul_one]
    _ = 1 * (1 + X) := by rw [hprod]
    _ = 1 + X := one_mul _

private lemma exp_neg_subst_log :
    PowerSeries.subst (PowerSeries.log ℚ) (PowerSeries.subst (-X : PowerSeries ℚ) (PowerSeries.exp ℚ)) = geomNeg := by
  have hnegX : HasSubst (-X : PowerSeries ℚ) := HasSubst.of_constantCoeff_zero' (by simp)
  have hlog : HasSubst (PowerSeries.log ℚ) := HasSubst.log
  set eNeg : PowerSeries ℚ := PowerSeries.subst (-X) (PowerSeries.exp ℚ)
  have hderiv_neg : d⁄dX ℚ eNeg = -eNeg := by
    change d⁄dX ℚ (PowerSeries.subst (-X) (PowerSeries.exp ℚ)) = -PowerSeries.subst (-X) (PowerSeries.exp ℚ)
    rw [PowerSeries.derivative_subst hnegX, PowerSeries.derivative_exp, map_neg,
      PowerSeries.derivative_X]
    ring
  have hprod : PowerSeries.subst (PowerSeries.log ℚ) eNeg * (1 + X) = 1 := by
    apply PowerSeries.derivative.ext
    · have hsubst_neg : PowerSeries.subst (PowerSeries.log ℚ) (-eNeg) =
          -(PowerSeries.subst (PowerSeries.log ℚ) eNeg) := by
        rw [← PowerSeries.coe_substAlgHom hlog, map_neg]
      rw [Derivation.map_one_eq_zero, Derivation.leibniz, PowerSeries.derivative_subst hlog,
        hderiv_neg, hsubst_neg, deriv_log_eq_geomNeg, map_add,
        Derivation.map_one_eq_zero, PowerSeries.derivative_X, zero_add]
      simp only [smul_eq_mul]
      calc PowerSeries.subst (PowerSeries.log ℚ) eNeg * 1 +
              (1 + X) * (-(PowerSeries.subst (PowerSeries.log ℚ) eNeg) * geomNeg)
          = PowerSeries.subst (PowerSeries.log ℚ) eNeg * (1 - geomNeg * (1 + X)) := by ring
        _ = 0 := by rw [geomNeg_mul_one_add_X, sub_self, mul_zero]
    · rw [map_mul, map_one, constantCoeff_subst_zero_arg PowerSeries.constantCoeff_log]
      have he0 : constantCoeff eNeg = 1 := by
        change constantCoeff (PowerSeries.subst (-X) (PowerSeries.exp ℚ)) = 1
        rw [constantCoeff_subst_zero_arg (by simp : constantCoeff (-X : PowerSeries ℚ) = 0),
          PowerSeries.constantCoeff_exp]
      rw [he0]
      simp
  calc PowerSeries.subst (PowerSeries.log ℚ) eNeg
      = (PowerSeries.subst (PowerSeries.log ℚ) eNeg * (1 + X)) * geomNeg := by
        rw [mul_assoc, mul_comm (1 + X) geomNeg, geomNeg_mul_one_add_X, mul_one]
    _ = 1 * geomNeg := by rw [hprod]
    _ = geomNeg := one_mul _

private lemma egf_eq :
    egf = ((1 + X) * PowerSeries.log ℚ - geomNeg * PowerSeries.log ℚ) * C (1 / 4 : ℚ) := by
  have hlog : HasSubst (PowerSeries.log ℚ) := HasSubst.log
  unfold egf sinhSeries
  rw [PowerSeries.subst_mul hlog, PowerSeries.subst_sub hlog, PowerSeries.subst_C,
    exp_subst_log, exp_neg_subst_log]
  have hC : (C (1 / 2 : ℚ) : PowerSeries ℚ) * C (1 / 2 : ℚ) = C (1 / 4 : ℚ) := by
    rw [← map_mul]; norm_num
  have hMvC : (MvPowerSeries.C (1 / 2 : ℚ) : PowerSeries ℚ) = C (1 / 2 : ℚ) := rfl
  rw [hMvC]
  calc ((1 + X - geomNeg) * C (1 / 2 : ℚ)) * PowerSeries.log ℚ * C (1 / 2 : ℚ)
      = ((1 + X) * PowerSeries.log ℚ - geomNeg * PowerSeries.log ℚ) * (C (1 / 2 : ℚ) * C (1 / 2 : ℚ)) := by ring
    _ = ((1 + X) * PowerSeries.log ℚ - geomNeg * PowerSeries.log ℚ) * C (1 / 4 : ℚ) := by rw [hC]

/-- Harmonic sum `H_n = ∑_{j=1}^n 1/j` as a rational number. -/
private def harm (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 n, (1 : ℚ) / (j : ℚ)

private lemma coeff_one_add_X_mul_log (n : ℕ) (hn : 2 ≤ n) :
    PowerSeries.coeff n ((1 + X) * PowerSeries.log ℚ) =
      (-1 : ℚ) ^ n / ((n : ℚ) * ((n - 1 : ℕ) : ℚ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [add_mul, one_mul, map_add, mul_comm X, PowerSeries.coeff_succ_mul_X,
    PowerSeries.coeff_log, PowerSeries.coeff_log, if_neg (by omega), if_neg (by omega)]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Nat.add_sub_cancel]
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm1 : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hp1 : (-1 : ℚ) ^ (m + 1 + 1) = -((-1 : ℚ) ^ (m + 1)) := by rw [pow_succ]; ring
  rw [hp1]
  push_cast
  field_simp [hm0, show (m : ℚ) + 1 ≠ 0 by positivity]
  ring

private lemma coeff_geomNeg_mul_log (n : ℕ) :
    PowerSeries.coeff n (geomNeg * PowerSeries.log ℚ) = -((-1 : ℚ) ^ n * harm n) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold harm
  have hsplit :
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff (n - k) geomNeg * PowerSeries.coeff k (PowerSeries.log ℚ) =
      ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (n - k) * ((-1 : ℚ) ^ (k + 1) / (k : ℚ)) := by
    have h0 : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [h0, Finset.sum_insert (by simp)]
    simp only [PowerSeries.coeff_log, ite_true, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    simp [geomNeg, show k ≠ 0 by omega]
  have hsymm :
      ∑ x ∈ Finset.range (n + 1),
        PowerSeries.coeff x geomNeg * PowerSeries.coeff (n - x) (PowerSeries.log ℚ) =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff (n - k) geomNeg * PowerSeries.coeff k (PowerSeries.log ℚ) := by
    refine Finset.sum_nbij (fun x => n - x) ?_ ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_range] at hx hy
      dsimp only at hxy
      omega
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_range] at hk
      exact ⟨n - k, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
    · intro x hx
      simp only [Finset.mem_range] at hx
      rw [show n - (n - x) = x by omega]
  rw [hsymm, hsplit, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hpow : (-1 : ℚ) ^ (n - k) * (-1 : ℚ) ^ (k + 1) = -((-1 : ℚ) ^ n) := by
    rw [← pow_add, show n - k + (k + 1) = n + 1 by omega, pow_succ]; ring
  rw [mul_div_assoc', hpow]
  ring

private lemma a_closed_form (n : ℕ) (hn : 2 ≤ n) :
    a n = (-1 : ℚ) ^ n * ((n.factorial : ℚ) * harm n + ((n - 2).factorial : ℚ)) / 4 := by
  unfold a
  rw [egf_eq, mul_comm _ (C (1 / 4 : ℚ)), PowerSeries.coeff_C_mul, map_sub,
    coeff_one_add_X_mul_log n hn, coeff_geomNeg_mul_log n]
  have hfac : (n.factorial : ℚ) = (n : ℚ) * ((n - 1 : ℕ) : ℚ) * ((n - 2).factorial : ℚ) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega, Nat.factorial_succ]
    push_cast; ring
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : ((n - 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hterm : (n.factorial : ℚ) * ((-1 : ℚ) ^ n / ((n : ℚ) * ((n - 1 : ℕ) : ℚ))) =
      (-1 : ℚ) ^ n * ((n - 2).factorial : ℚ) := by
    rw [hfac]
    field_simp [hn0, hn1]
  linarith

private def U (n : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (n + 1), (m : ℚ) * (Nat.stirlingFirst n m : ℚ)

private def V (n : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (n + 1), (-1 : ℚ) ^ m * (m : ℚ) * (Nat.stirlingFirst n m : ℚ)

private lemma sum_stirlingFirst_eq_factorial (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (Nat.stirlingFirst n m : ℚ) = (n.factorial : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.stirlingFirst_succ_zero, Nat.cast_zero, add_zero]
    have hrec : ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst (n + 1) (k + 1) : ℚ) =
        (n : ℚ) * (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n (k + 1) : ℚ)) +
        ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℚ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.stirlingFirst_succ_succ]; push_cast; ring
    rw [hrec, ih]
    cases n with
    | zero => simp
    | succ m =>
      have hshift : ∑ k ∈ Finset.range (m + 2), (Nat.stirlingFirst (m + 1) (k + 1) : ℚ) =
          ((m + 1).factorial : ℚ) := by
        rw [Finset.sum_range_succ, Nat.stirlingFirst_eq_zero_of_lt (by omega : m + 1 < m + 2),
          Nat.cast_zero, add_zero]
        have h0 := ih
        rw [Finset.sum_range_succ'] at h0
        simpa [Nat.stirlingFirst_succ_zero] using h0
      rw [hshift]
      have hfac : ((m + 2).factorial : ℚ) = ((m + 1 : ℕ) + 1 : ℚ) * ((m + 1).factorial : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [hfac]; push_cast; ring

private lemma sum_alt_stirlingFirst (n : ℕ) (hn : 2 ≤ n) :
    ∑ m ∈ Finset.range (n + 1), (-1 : ℚ) ^ m * (Nat.stirlingFirst n m : ℚ) = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero =>
        simp [Finset.sum_range_succ, Nat.stirlingFirst]
      | succ k =>
        have ih' := ih (by omega)
        rw [Finset.sum_range_succ']
        simp only [Nat.stirlingFirst_succ_zero, Nat.cast_zero, mul_zero, add_zero]
        have hrec :
            ∑ j ∈ Finset.range (k + 3), (-1 : ℚ) ^ (j + 1) * (Nat.stirlingFirst (k + 3) (j + 1) : ℚ) =
            ((k + 2 : ℕ) : ℚ) * (∑ j ∈ Finset.range (k + 3), (-1 : ℚ) ^ (j + 1) * (Nat.stirlingFirst (k + 2) (j + 1) : ℚ)) -
            ∑ j ∈ Finset.range (k + 3), (-1 : ℚ) ^ j * (Nat.stirlingFirst (k + 2) j : ℚ) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Nat.stirlingFirst_succ_succ, pow_succ]
          push_cast; ring
        rw [hrec, ih', sub_zero]
        have hshift :
            ∑ j ∈ Finset.range (k + 3), (-1 : ℚ) ^ (j + 1) * (Nat.stirlingFirst (k + 2) (j + 1) : ℚ) = 0 := by
          rw [Finset.sum_range_succ, Nat.stirlingFirst_eq_zero_of_lt (by omega : k + 2 < k + 3),
            Nat.cast_zero, mul_zero, add_zero]
          have h0 := ih'
          rw [Finset.sum_range_succ'] at h0
          simpa [Nat.stirlingFirst_succ_zero] using h0
        rw [hshift, mul_zero]

private lemma U_eq (n : ℕ) : U n = (n.factorial : ℚ) * harm n := by
  induction n with
  | zero => simp [U, harm]
  | succ n ih =>
    unfold U
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hsplit :
        ∑ k ∈ Finset.range (n + 1), ((k + 1 : ℕ) : ℚ) * (Nat.stirlingFirst (n + 1) (k + 1) : ℚ) =
        (n : ℚ) * (∑ k ∈ Finset.range (n + 1), ((k + 1 : ℕ) : ℚ) * (Nat.stirlingFirst n (k + 1) : ℚ)) +
        (∑ k ∈ Finset.range (n + 1), (k : ℚ) * (Nat.stirlingFirst n k : ℚ)) +
        ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℚ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.stirlingFirst_succ_succ]; push_cast; ring
    have hUshift :
        ∑ k ∈ Finset.range (n + 1), ((k + 1 : ℕ) : ℚ) * (Nat.stirlingFirst n (k + 1) : ℚ) = U n := by
      rw [Finset.sum_range_succ, Nat.stirlingFirst_eq_zero_of_lt (by omega : n < n + 1),
        Nat.cast_zero, mul_zero, add_zero]
      unfold U
      rw [Finset.sum_range_succ']
      simp
    rw [hsplit, hUshift, show (∑ k ∈ Finset.range (n + 1), (k : ℚ) * (Nat.stirlingFirst n k : ℚ)) = U n from rfl,
      sum_stirlingFirst_eq_factorial, ih]
    have hharm : harm (n + 1) = harm n + 1 / ((n + 1 : ℕ) : ℚ) := by
      unfold harm
      have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]; ring
    rw [hharm, Nat.factorial_succ]
    have hne : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    field_simp [hne]

private lemma V_eq (n : ℕ) (hn : 2 ≤ n) : V n = ((n - 2).factorial : ℚ) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero =>
        simp [V, Finset.sum_range_succ, Nat.stirlingFirst]
        norm_num
      | succ k =>
        have ih' := ih (by omega)
        unfold V
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
        have hsplit :
            ∑ j ∈ Finset.range (k + 3),
              (-1 : ℚ) ^ (j + 1) * ((j + 1 : ℕ) : ℚ) * (Nat.stirlingFirst (k + 3) (j + 1) : ℚ) =
            ((k + 2 : ℕ) : ℚ) * (∑ j ∈ Finset.range (k + 3),
              (-1 : ℚ) ^ (j + 1) * ((j + 1 : ℕ) : ℚ) * (Nat.stirlingFirst (k + 2) (j + 1) : ℚ)) -
            (∑ j ∈ Finset.range (k + 3), (-1 : ℚ) ^ j * (j : ℚ) * (Nat.stirlingFirst (k + 2) j : ℚ)) -
            ∑ j ∈ Finset.range (k + 3), (-1 : ℚ) ^ j * (Nat.stirlingFirst (k + 2) j : ℚ) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Nat.stirlingFirst_succ_succ, pow_succ]
          push_cast; ring
        have hVshift :
            ∑ j ∈ Finset.range (k + 3),
              (-1 : ℚ) ^ (j + 1) * ((j + 1 : ℕ) : ℚ) * (Nat.stirlingFirst (k + 2) (j + 1) : ℚ) = V (k + 2) := by
          rw [Finset.sum_range_succ, Nat.stirlingFirst_eq_zero_of_lt (by omega : k + 2 < k + 3),
            Nat.cast_zero, mul_zero, add_zero]
          symm
          unfold V
          rw [Finset.sum_range_succ']
          simp
        rw [hsplit, hVshift,
          show (∑ j ∈ Finset.range (k + 3), (-1 : ℚ) ^ j * (j : ℚ) * (Nat.stirlingFirst (k + 2) j : ℚ)) = V (k + 2) from rfl,
          sum_alt_stirlingFirst (k + 2) (by omega), sub_zero, ih']
        have hsub1 : k + 2 - 2 = k := by omega
        have hsub2 : k + 3 - 2 = k + 1 := by omega
        rw [hsub1, hsub2, Nat.factorial_succ]
        push_cast; ring

private lemma rhs_eq_UV (n : ℕ) :
    (∑ k ∈ Finset.range (n / 2 + 1), (signedStirlingFirst n (2 * k) * (k : ℤ) : ℚ)) =
      (-1 : ℚ) ^ n * (U n + V n) / 4 := by
  have hUV : U n + V n =
      ∑ m ∈ Finset.range (n + 1), (1 + (-1 : ℚ) ^ m) * (m : ℚ) * (Nat.stirlingFirst n m : ℚ) := by
    unfold U V
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => by ring
  have hsum :
      ∑ m ∈ Finset.range (n + 1), (1 + (-1 : ℚ) ^ m) * (m : ℚ) * (Nat.stirlingFirst n m : ℚ) =
      4 * ∑ k ∈ Finset.range (n / 2 + 1), (k : ℚ) * (Nat.stirlingFirst n (2 * k) : ℚ) := by
    rw [Finset.mul_sum]
    have hsplit :
        ∑ m ∈ Finset.range (n + 1), (1 + (-1 : ℚ) ^ m) * (m : ℚ) * (Nat.stirlingFirst n m : ℚ) =
        ∑ m ∈ (Finset.range (n + 1)).filter Even,
          (1 + (-1 : ℚ) ^ m) * (m : ℚ) * (Nat.stirlingFirst n m : ℚ) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) Even]
      have hodd :
          ∑ m ∈ (Finset.range (n + 1)).filter (fun m => ¬ Even m),
            (1 + (-1 : ℚ) ^ m) * (m : ℚ) * (Nat.stirlingFirst n m : ℚ) = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        have hmo : Odd m := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hm).2
        rw [hmo.neg_one_pow]; ring
      rw [hodd, add_zero]
    rw [hsplit]
    refine Finset.sum_nbij (fun m => m / 2) ?_ ?_ ?_ ?_
    · intro m hm
      have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
    · intro m1 hm1 m2 hm2 heq
      obtain ⟨k1, hk1⟩ := (Finset.mem_filter.mp hm1).2
      obtain ⟨k2, hk2⟩ := (Finset.mem_filter.mp hm2).2
      dsimp only at heq
      omega
    · intro k hk
      have hlt := Finset.mem_range.mp hk
      refine ⟨2 * k, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨k, by omega⟩⟩), ?_⟩
      dsimp only; omega
    · intro m hm
      obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hm).2
      have hdiv : m / 2 = k := by omega
      have h2k : 2 * (m / 2) = m := by omega
      rw [h2k, hk, show k + k = 2 * k by omega, pow_mul]
      norm_num
      ring
  rw [hUV, hsum]
  have hrhs_cast :
      (∑ k ∈ Finset.range (n / 2 + 1), (signedStirlingFirst n (2 * k) * (k : ℤ) : ℚ)) =
      (-1 : ℚ) ^ n * ∑ k ∈ Finset.range (n / 2 + 1), (k : ℚ) * (Nat.stirlingFirst n (2 * k) : ℚ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    unfold signedStirlingFirst
    have hlt : k < n / 2 + 1 := Finset.mem_range.mp hk
    have h2kle : 2 * k ≤ n := by omega
    have hpow : ((-1 : ℤ) ^ (n - 2 * k) : ℚ) = (-1 : ℚ) ^ n := by
      push_cast
      have hpar : (-1 : ℚ) ^ (n - 2 * k) * (-1 : ℚ) ^ (2 * k) = (-1 : ℚ) ^ n := by
        rw [← pow_add, Nat.sub_add_cancel h2kle]
      have hev : (-1 : ℚ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
      rw [hev, mul_one] at hpar
      exact hpar
    push_cast
    rw [show (-1 : ℚ) ^ (n - 2 * k) = (-1 : ℚ) ^ n by simpa using hpow]
    ring
  rw [hrhs_cast]
  ring

private lemma main_proof : ∀ n : ℕ,
    a n = ∑ k ∈ Finset.range (n / 2 + 1), (signedStirlingFirst n (2 * k) * (k : ℤ) : ℚ) := by
  intro n
  rcases n with _ | _ | n
  · unfold a
    rw [egf_eq]
    simp [signedStirlingFirst]
  · unfold a
    rw [egf_eq, mul_comm _ (C (1 / 4 : ℚ)), PowerSeries.coeff_C_mul, map_sub]
    have h1 : PowerSeries.coeff 1 ((1 + X) * PowerSeries.log ℚ) = 1 := by
      rw [add_mul, one_mul, map_add, mul_comm X, PowerSeries.coeff_succ_mul_X]
      simp [PowerSeries.coeff_log]
    have h2 : PowerSeries.coeff 1 (geomNeg * PowerSeries.log ℚ) = 1 := by
      rw [coeff_geomNeg_mul_log 1]; simp [harm]
    rw [h1, h2]
    simp [signedStirlingFirst]
  · rw [a_closed_form (n + 2) (by omega), rhs_eq_UV (n + 2), U_eq (n + 2), V_eq (n + 2) (by omega)]

end OMA.Proof_oeis_a024337

theorem OMA.solution : type_of% @OMA.S_oeis_a024337.main :=
  OMA.Proof_oeis_a024337.main_proof
