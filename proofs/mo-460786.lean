import OMAStatements.S_mo_460786

private noncomputable def F : ℕ → PowerSeries ℚ
  | 0 => 1
  | n + 1 => PowerSeries.derivative (R := ℚ) (OMA.S_mo_460786.rhs * F n)

private theorem coeff_F (n q : ℕ) :
    PowerSeries.coeff q (F n) = (OMA.S_mo_460786.R n q : ℚ) / (q.factorial : ℚ) := by
  induction n generalizing q with
  | zero =>
    cases q with
    | zero => simp [F, OMA.S_mo_460786.R]
    | succ q => simp [F, OMA.S_mo_460786.R]
  | succ n ih =>
    have hsplit : F (n + 1) =
        PowerSeries.derivative (R := ℚ) (F n) +
          PowerSeries.derivative (R := ℚ) (PowerSeries.X * (F n * PowerSeries.exp ℚ)) := by
      simp only [F, OMA.S_mo_460786.rhs, add_mul, one_mul, map_add, mul_assoc,
        mul_comm (PowerSeries.exp ℚ) (F n)]
    rw [hsplit, map_add, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
      PowerSeries.coeff_succ_X_mul, ih (q + 1), PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun j k => PowerSeries.coeff j (F n) * PowerSeries.coeff k (PowerSeries.exp ℚ))]
    have hsum : ∑ j ∈ Finset.range (q + 1),
        PowerSeries.coeff j (F n) * PowerSeries.coeff (q - j) (PowerSeries.exp ℚ) =
        (∑ j ∈ Finset.range (q + 1), (q.choose j : ℚ) * (OMA.S_mo_460786.R n j : ℚ)) /
          (q.factorial : ℚ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjle : j ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [ih j, PowerSeries.coeff_exp]
      simp only [Algebra.algebraMap_self, RingHom.id_apply, one_div]
      have hch : (q.choose j : ℚ) * (j.factorial : ℚ) * ((q - j).factorial : ℚ) =
          (q.factorial : ℚ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjle
      have hqfac : (q.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
      have hjfac : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      have hqjfac : ((q - j).factorial : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (q - j))
      field_simp
      rw [← hch]
      ring
    rw [hsum]
    have hqfac : (q.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
    have hq1 : (q : ℚ) + 1 ≠ 0 := by positivity
    rw [Nat.factorial_succ]
    simp only [OMA.S_mo_460786.R, Nat.cast_add, Nat.cast_mul, Nat.cast_sum]
    field_simp
    ring

private theorem iterate_deriv_A (A : PowerSeries ℚ) (hA0 : A.constantCoeff = 0)
    (hAd : PowerSeries.derivative (R := ℚ) A = OMA.S_mo_460786.rhs.subst A) (n : ℕ) :
    (PowerSeries.derivative (R := ℚ))^[n + 1] A = (OMA.S_mo_460786.rhs * F n).subst A := by
  induction n with
  | zero =>
    simp [F, hAd]
  | succ n ih =>
    have hA : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' hA0
    rw [Function.iterate_succ_apply', ih, PowerSeries.derivative_subst hA, hAd,
      ← PowerSeries.subst_mul hA, mul_comm (OMA.S_mo_460786.rhs) (F (n + 1))]
    rfl

theorem OMA.solution : type_of% @OMA.S_mo_460786.main := by
  intro A hA0 hAd n
  have hiter := iterate_deriv_A A hA0 hAd n
  have hc := congrArg PowerSeries.constantCoeff hiter
  rw [PowerSeries.constantCoeff_iterate_derivative] at hc
  have hA : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  have hsubst : ∀ g : PowerSeries ℚ, PowerSeries.constantCoeff (g.subst A) = g.constantCoeff := by
    intro g
    have hsub : PowerSeries.constantCoeff (g - PowerSeries.C g.constantCoeff) = 0 := by
      rw [map_sub, PowerSeries.constantCoeff_C, sub_self]
    have h0 : PowerSeries.constantCoeff ((g - PowerSeries.C g.constantCoeff).subst A) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hA0 _ hsub
    have hC : PowerSeries.constantCoeff ((PowerSeries.C g.constantCoeff).subst A) =
        g.constantCoeff := by
      rw [PowerSeries.subst_C]
      exact PowerSeries.constantCoeff_C g.constantCoeff
    have hg : g = PowerSeries.C g.constantCoeff + (g - PowerSeries.C g.constantCoeff) := by ring
    conv_lhs => rw [hg, PowerSeries.subst_add hA, map_add, hC, h0, add_zero]
  rw [hsubst, map_mul] at hc
  have hrhs : PowerSeries.constantCoeff OMA.S_mo_460786.rhs = 1 := by
    simp [OMA.S_mo_460786.rhs]
  have hFn : PowerSeries.constantCoeff (F n) = (OMA.S_mo_460786.R n 0 : ℚ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_F]
    simp
  rw [hrhs, hFn, one_mul] at hc
  exact hc.symm
