import OMAReductions.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1

/-! The elementary part of the relative analytic class-number formula
used in Sawin's Lemma 9. -/
namespace OMA.ResidueSawin90
open NumberField NumberField.Units NumberField.InfinitePlace Real Module
open scoped NumberField

private theorem ratio (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    let F := maximalRealSubfield K
    (2*π)^finrank ℚ F * sqrt |(discr F : ℝ)| * (classNumber K : ℝ) *
        dedekindZeta_residue F ≤
      (IsCMField.indexRealUnits K : ℝ) * torsionOrder K * sqrt |(discr K : ℝ)| *
        classNumber F * dedekindZeta_residue K := by
  let F := maximalRealSubfield K
  change (2*π)^finrank ℚ F * _ * _ * _ ≤ _
  let d := finrank ℚ F
  have pos : 0 < d := finrank_pos
  have cr : nrComplexPlaces K = d := by
    have h := IsTotallyComplex.finrank K
    rw [← finrank_mul_finrank ℚ F K, Algebra.IsQuadraticExtension.finrank_eq_two F K] at h
    omega
  have rk : Units.rank K + 1 = d := by
    rw [Units.rank,card_eq_nrRealPlaces_add_nrComplexPlaces,IsTotallyComplex.nrRealPlaces_eq_zero,
      zero_add,cr]
    omega
  have powrel : (2:ℝ)^d = 2^Units.rank K*2 := by rw [←rk,pow_succ]
  have ri := IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv K
  have qp : 0 < (IsCMField.indexRealUnits K : ℝ) := by
    rcases IsCMField.indexRealUnits_eq_one_or_two K with h|h <;> rw [h] <;> norm_num
  have rr : regulator K * (IsCMField.indexRealUnits K : ℝ) = 2^Units.rank K * regulator F := by
    change regulator K / regulator F = _ at ri
    field_simp [regulator_ne_zero F,qp.ne'] at ri
    linarith
  have wp : 2 ≤ torsionOrder F := by
    have h := even_iff_two_dvd.mp (even_torsionOrder F)
    exact Nat.le_of_dvd (torsionOrder_pos F) h
  have low : (2:ℝ) ≤ torsionOrder F := by exact_mod_cast wp
  have sF : 0 < sqrt |(discr F : ℝ)| := Real.sqrt_pos.mpr
    (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F)))
  have sK : 0 < sqrt |(discr K : ℝ)| := Real.sqrt_pos.mpr
    (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))
  have wF : 0 < (torsionOrder F : ℝ) := Nat.cast_pos.mpr (torsionOrder_pos F)
  have wK : 0 < (torsionOrder K : ℝ) := Nat.cast_pos.mpr (torsionOrder_pos K)
  have realP : nrRealPlaces F = d := (IsTotallyReal.finrank F).symm
  change (2*π)^d * sqrt _ * _ * dedekindZeta_residue F ≤ _ * _ * sqrt _ * _ * dedekindZeta_residue K
  rw [dedekindZeta_residue_def F,dedekindZeta_residue_def K,realP,
    IsTotallyReal.nrComplexPlaces_eq_zero,IsTotallyComplex.nrRealPlaces_eq_zero,cr]
  simp only [pow_zero, mul_one, one_mul]
  field_simp [wF.ne',wK.ne',sK.ne',sF.ne']
  rw [powrel]
  let C := sqrt |(discr F : ℝ)| * (classNumber K : ℝ) * (classNumber F : ℝ)
  have nonneg : 0 ≤ C * (2^Units.rank K * regulator F) := by
    dsimp [C]
    have := regulator_pos F
    positivity
  calc _ = (C * (2^Units.rank K * regulator F))*2 := by dsimp [C,F]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left low nonneg
       _ = _ := by rw [← rr]; dsimp [C,F]; ring

private theorem from_residue (K : Type*) [Field K] [NumberField K] [IsCMField K]
    (lam : ℝ) (hl : 1 < lam)
    (hr : |(discr K : ℝ)| / |(discr (maximalRealSubfield K) : ℝ)| ≤
      lam ^ finrank ℚ (maximalRealSubfield K))
    (roots : (torsionOrder K : ℝ) ≤ 2*lam^2)
    (zeta : dedekindZeta_residue K ≤ dedekindZeta_residue (maximalRealSubfield K) *
      (2 * (exp 1 * log lam / 2) ^ finrank ℚ (maximalRealSubfield K))) :
    (classNumber K : ℝ) ≤ (classNumber (maximalRealSubfield K) : ℝ) *
      (8 * lam^2 * (sqrt lam * log lam * (exp 1 / (4 * π)))^finrank ℚ (maximalRealSubfield K)) := by
  let F := maximalRealSubfield K
  let d := finrank ℚ F
  change _ / |(discr F : ℝ)| ≤ lam^d at hr
  change _ ≤ dedekindZeta_residue F * (2 * (exp 1 * log lam / 2)^d) at zeta
  change _ ≤ (classNumber F : ℝ) * (8 * lam^2 * _^d)
  have posF : 0 < |(discr F : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F))
  have sqrtpos : 0 < sqrt |(discr F : ℝ)| := Real.sqrt_pos.mpr posF
  have dcap := (div_le_iff₀ posF).mp hr
  have sp (m : ℕ) : sqrt (lam^m) = (sqrt lam)^m := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg (by linarith) _),ih,pow_succ]
  have sc : sqrt |(discr K : ℝ)| ≤ sqrt |(discr F : ℝ)| * (sqrt lam)^d := by
    calc _ ≤ sqrt (lam^d * |(discr F : ℝ)|) := Real.sqrt_le_sqrt dcap
         _ = _ := by rw [mul_comm,Real.sqrt_mul posF.le,sp]
  have qi : (IsCMField.indexRealUnits K : ℝ) ≤ 2 := by
    rcases IsCMField.indexRealUnits_eq_one_or_two K with h|h <;> rw [h] <;> norm_num
  have lc : 0 < log lam := Real.log_pos hl
  have rf := dedekindZeta_residue_pos F
  have rk := dedekindZeta_residue_pos K
  have hK := ratio K
  change (2*π)^d * sqrt |(discr F : ℝ)| * (classNumber K:ℝ) * dedekindZeta_residue F ≤
    (IsCMField.indexRealUnits K:ℝ) * torsionOrder K * sqrt |(discr K : ℝ)| *
    classNumber F * dedekindZeta_residue K at hK
  have powers : (2*π)^d * (sqrt lam * log lam * (exp 1 / (4*π)))^d =
      (sqrt lam)^d * (exp 1 * log lam/2)^d := by
    rw [←mul_pow,←mul_pow]
    congr 1
    field_simp
    ring
  let A := (2*π)^d * sqrt |(discr F : ℝ)| * dedekindZeta_residue F
  have Ap : 0 < A := by dsimp [A]; positivity
  apply le_of_mul_le_mul_left (a := A) _ Ap
  calc _ = (2*π)^d * sqrt |(discr F : ℝ)| * (classNumber K:ℝ) * dedekindZeta_residue F := by
         dsimp [A]; ring
       _ ≤ _ := hK
       _ ≤ (2:ℝ) * (2*lam^2) * (sqrt |(discr F : ℝ)| * (sqrt lam)^d) * classNumber F *
             (dedekindZeta_residue F * (2 * (exp 1 * log lam / 2)^d)) := by gcongr
       _ = (sqrt |(discr F : ℝ)| * dedekindZeta_residue F) *
           ((classNumber F : ℝ) * (8*lam^2)) * ((sqrt lam)^d * (exp 1 * log lam/2)^d) := by ring
       _ = _ := by rw [←powers]; dsimp [A]; ring

theorem transfer (F K : Type*) [Field F] [NumberField F] [IsTotallyReal F]
    [Field K] [NumberField K] [IsTotallyComplex K] [Algebra F K]
    [Algebra.IsQuadraticExtension F K] (lam : ℝ) (hl : 1 < lam)
    (hr : |(discr K : ℝ)| / |(discr F : ℝ)| ≤ lam^finrank ℚ F)
    (roots : (torsionOrder K : ℝ) ≤ 2*lam^2)
    (analytic : dedekindZeta_residue K ≤ dedekindZeta_residue (maximalRealSubfield K) *
      (2 * (exp 1 * log lam / 2)^finrank ℚ F)) :
    (classNumber K : ℝ) ≤ (classNumber F : ℝ) *
      (8*lam^2*(sqrt lam*log lam*(exp 1/(4*π)))^finrank ℚ F) := by
  let : IsCMField K := IsCMField.ofCMExtension F K
  let e := CMExtension.equivMaximalRealSubfield F K
  have dim := e.toRatAlgEquiv.toLinearEquiv.finrank_eq
  have hd := discr_eq_discr_of_algEquiv F e.toRatAlgEquiv
  have hc : classNumber F = classNumber (maximalRealSubfield K) :=
    Fintype.card_congr (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e)).toEquiv
  rw [dim,hd] at hr
  rw [dim] at analytic
  rw [hc,dim]
  exact from_residue K lam hl hr roots analytic

/-- Monotonicity in the supplied root-discriminant bound, starting from the
actual log-conductor expression in Louboutin's Theorem 2. -/
theorem analytic_cap (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (lam : ℝ)
    (hr : |(discr K : ℝ)| / |(discr F : ℝ)| ≤ lam^finrank ℚ F)
    (bound : dedekindZeta_residue K ≤ dedekindZeta_residue F *
      (2 * (exp 1 * log (|(discr K : ℝ)| / |(discr F : ℝ)|) /
        (2 * (finrank ℚ F : ℝ)))^finrank ℚ F)) :
    dedekindZeta_residue K ≤ dedekindZeta_residue F * (2*(exp 1*log lam/2)^finrank ℚ F) := by
  let D := |(discr K : ℝ)| / |(discr F : ℝ)|
  have d : 0 < (finrank ℚ F : ℝ) := Nat.cast_pos.mpr finrank_pos
  have dp : 0 < D := div_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))
    (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F)))
  have hdiv := discr_dvd_discr F K
  have hsize := Nat.le_of_dvd (Int.natAbs_pos.mpr (discr_ne_zero K)) (Int.natAbs_dvd_natAbs.mpr hdiv)
  have hD : 1 ≤ D := by
    apply (one_le_div (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F)))).mpr
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (show ((discr F).natAbs : ℝ) ≤ ((discr K).natAbs : ℝ) by exact_mod_cast hsize)
  have logs := Real.log_le_log dp hr
  rw [Real.log_pow] at logs
  change _ ≤ dedekindZeta_residue F * (2*(exp 1*log D/(2 * (finrank ℚ F:ℝ)))^_) at bound
  have h : exp 1 * log D / (2*(finrank ℚ F : ℝ)) ≤ exp 1 * log lam / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc _ ≤ exp 1 * ((finrank ℚ F : ℝ)*log lam) := mul_le_mul_of_nonneg_left logs (exp_pos _).le
         _ = _ := by ring
  have p : 0 ≤ exp 1*log D/(2*(finrank ℚ F:ℝ)) :=
    div_nonneg (mul_nonneg (exp_pos _).le (Real.log_nonneg hD)) (by positivity)
  exact bound.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ p h _) (by norm_num)) (dedekindZeta_residue_pos F).le)

end OMA.ResidueSawin90

/- Reduction of Will Sawin's Lemma 9 to the cyclotomic discriminant and the
analytic estimate for a quadratic Hecke character (Stéphane Louboutin,
"Explicit Bounds for Residues of Dedekind Zeta Functions, Values of L-Functions
at s=1, and Relative Class Numbers", J. Number Theory 85 (2000), Theorem 2). -/
namespace OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1_H3_R1
open NumberField NumberField.Units Real Module

/-- Size of the group of roots of unity, in terms of the relative discriminant. -/
def H1 : Prop :=
  ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K] (lam : ℝ), 1 < lam →
    |(discr K : ℝ)| / |(discr F : ℝ)| ≤ lam ^ finrank ℚ F →
    (torsionOrder K : ℝ) ≤ 2*lam^2

/-- Louboutin's bound for the value at one of the quadratic Hecke L-function
of a CM extension, expressed as the ratio of the two Dedekind zeta residues. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    let F := maximalRealSubfield K
    let d := finrank ℚ F
    dedekindZeta_residue K ≤ dedekindZeta_residue F *
      (2 * (exp 1 * log (|(discr K : ℝ)| / |(discr F : ℝ)|) / (2*(d : ℝ)))^d)

theorem main : H1 → H2 → OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1.H3 := by
  intro roots lfun F K _ _ _ _ _ _ _ _ _ _ lam hl hdisc
  let : IsCMField K := IsCMField.ofCMExtension F K
  let e := CMExtension.equivMaximalRealSubfield F K
  have dim := e.toRatAlgEquiv.toLinearEquiv.finrank_eq
  have hd := discr_eq_discr_of_algEquiv F e.toRatAlgEquiv
  apply OMA.ResidueSawin90.transfer F K lam hl hdisc (roots F K lam hl hdisc)
  rw [dim]
  apply OMA.ResidueSawin90.analytic_cap (maximalRealSubfield K) K lam _ (lfun K)
  simpa only [← dim, ← hd] using hdisc

end OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1_H3_R1
