import OMAReductions.R_Firoozbakht_firoozbakht_conjecture_consequence_R1
import Mathlib

/-! # A prime-counting comparison from explicit Chebyshev estimates

Above the integral anchor at 90,000,000, apply the Abel summation formula
in Mathlib and compare derivatives with x / (log x - 1 - 1 / log x).
The required theta estimate follows from Dusart, Explicit estimates of
some functions over primes, Theorem 4.2, k = 3 and eta = 1, with threshold
89,967,803. The remaining computations are an integer certificate below
the anchor and one integer lower bound for its prime count. -/

namespace OMA.FiroozbakhtPrimeCount

private theorem xpos_log_ne_zero {x : ℝ} (hx : 12 ≤ Real.log x) : x ≠ 0 := by
  rintro rfl
  simp only [Real.log_zero] at hx
  linarith

private theorem quadratic_pos {L : ℝ} (hL : 12 ≤ L) : 0 < L^2-L-1 := by
  have h : 0 ≤ (L-2)*(L+1) := mul_nonneg (by linarith) (by linarith)
  nlinarith only [h]

/-- The exact quotient-rule derivative written in terms of its logarithm. -/
theorem hasDerivAt_countComparison {x : ℝ} (hx : 12 ≤ Real.log x) :
    HasDerivAt (fun t : ℝ => t/(Real.log t-1-1/Real.log t))
      (((Real.log x)^3-2*(Real.log x)^2-Real.log x-1) /
        ((Real.log x)^2-Real.log x-1)^2) x := by
  let L := Real.log x
  let Q := L^2-L-1
  have hL : 0 < L := (show (0:ℝ) < 12 by norm_num).trans_le hx
  have hQ : 0 < Q := quadratic_pos hx
  have hne : x ≠ 0 := xpos_log_ne_zero hx
  have hu : L-1-L⁻¹ = Q/L := by
    dsimp only [Q]
    field_simp [hL.ne']
  have hden : L-1-L⁻¹ ≠ 0 := by rw [hu]; exact (div_pos hQ hL).ne'
  have hlog := Real.hasDerivAt_log hne
  have hsub : HasDerivAt (fun t : ℝ => Real.log t-1-(Real.log t)⁻¹)
      (x⁻¹ - (-x⁻¹ / L^2)) x :=
    (hlog.sub_const 1).sub (hlog.inv hL.ne')
  have hdiv := (hasDerivAt_id' x).fun_div hsub hden
  have hval : (1*(L-1-L⁻¹)-x*(x⁻¹-(-x⁻¹/L^2)))/(L-1-L⁻¹)^2 =
      (L^3-2*L^2-L-1)/Q^2 := by
    rw [hu]
    dsimp only [Q]
    field_simp [hne,hL.ne',hQ.ne']
    ring
  change HasDerivAt (fun t : ℝ => t/(Real.log t-1-(Real.log t)⁻¹))
    ((1*(L-1-L⁻¹)-x*(x⁻¹-(-x⁻¹/L^2)))/(L-1-L⁻¹)^2) x at hdiv
  rw [hval] at hdiv
  simpa only [one_div] using hdiv

/-- A sharp convenient upper bound for the derivative of the comparison. -/
theorem deriv_countComparison_le {x : ℝ} (hx : 12 ≤ Real.log x) :
    deriv (fun t : ℝ => t/(Real.log t-1-1/Real.log t)) x ≤
      1/Real.log x - 3/(Real.log x)^4 := by
  rw [(hasDerivAt_countComparison hx).deriv]
  let L := Real.log x
  let Q := L^2-L-1
  have hL : 0 < L := (show (0:ℝ) < 12 by norm_num).trans_le hx
  have hQ : 0 < Q := quadratic_pos hx
  have hQle : Q ≤ L^2 := by dsimp only [Q]; linarith only [hL]
  have hs : Q^2 ≤ L^4 := by
    calc
      _ ≤ (L^2)^2 := pow_le_pow_left₀ hQ.le hQle 2
      _ = _ := by ring
  have hfrac : (L^3-2*L^2-L-1)/Q^2 = 1/L - (3*L+1)/(L*Q^2) := by
    field_simp [hL.ne',hQ.ne']
    dsimp only [Q]
    ring
  have hgap : 3/L^4 ≤ (3*L+1)/(L*Q^2) := by
    apply (div_le_div_iff₀ (pow_pos hL _) (mul_pos hL (pow_pos hQ _))).mpr
    calc
      3*(L*Q^2) = (3*L)*Q^2 := by ring
      _ ≤ (3*L)*L^4 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ (3*L+1)*L^4 := mul_le_mul_of_nonneg_right
        (by linarith) (pow_nonneg hL.le _)
  change (L^3-2*L^2-L-1)/Q^2 ≤ 1/L - 3/L^4
  rw [hfrac]
  exact sub_le_sub_left hgap _

/-- The derivative of the direct main term from a lower bound on theta. -/
theorem hasDerivAt_thetaComparison {x : ℝ} (hx : 12 ≤ Real.log x) :
    HasDerivAt (fun t : ℝ => (t-t/(Real.log t)^3)/Real.log t)
      (1/Real.log x-1/(Real.log x)^2-1/(Real.log x)^4+4/(Real.log x)^5) x := by
  let L := Real.log x
  have hL : 0 < L := (show (0:ℝ) < 12 by norm_num).trans_le hx
  have hne : x ≠ 0 := xpos_log_ne_zero hx
  have hlog := Real.hasDerivAt_log hne
  have hpow : HasDerivAt (fun t : ℝ => (Real.log t)^3) (3*L^2*x⁻¹) x :=
    hlog.fun_pow 3
  have htheta : HasDerivAt (fun t : ℝ => t-t/(Real.log t)^3)
      (1-(1*L^3-x*(3*L^2*x⁻¹))/(L^3)^2) x :=
    (hasDerivAt_id' x).fun_sub ((hasDerivAt_id' x).fun_div hpow (pow_ne_zero 3 hL.ne'))
  have hval :
      ((1-(1*L^3-x*(3*L^2*x⁻¹))/(L^3)^2)*L-(x-x/L^3)*x⁻¹)/L^2 =
        1/L-1/L^2-1/L^4+4/L^5 := by
    field_simp [hne,hL.ne']
    ring
  have hdiv : HasDerivAt (fun t : ℝ => (t-t/(Real.log t)^3)/Real.log t)
      (((1-(1*L^3-x*(3*L^2*x⁻¹))/(L^3)^2)*L-(x-x/L^3)*x⁻¹)/L^2) x :=
    htheta.fun_div hlog hL.ne'
  rw [hval] at hdiv
  exact hdiv

/-- The derivative of the difference used in partial summation. -/
theorem hasDerivAt_countComparison_sub_theta {x : ℝ} (hx : 12 ≤ Real.log x) :
    HasDerivAt (fun t : ℝ =>
      t/(Real.log t-1-1/Real.log t) - (t-t/(Real.log t)^3)/Real.log t)
      (((Real.log x)^3-2*(Real.log x)^2-Real.log x-1) /
        ((Real.log x)^2-Real.log x-1)^2 -
        (1/Real.log x-1/(Real.log x)^2-1/(Real.log x)^4+4/(Real.log x)^5)) x :=
  (hasDerivAt_countComparison hx).fun_sub (hasDerivAt_thetaComparison hx)

private theorem log_ge_of_mem_Ici {A x : ℝ} (hA : 2 ≤ A) (hlog : 12 ≤ Real.log A)
    (hx : x ∈ Set.Ici A) : 12 ≤ Real.log x :=
  hlog.trans (Real.log_le_log (by linarith) hx)

/-- The explicit derivative formula is continuous on the range of partial summation. -/
theorem continuousOn_countComparison_sub_theta_derivFormula {A : ℝ}
    (hA : 2 ≤ A) (hlog : 12 ≤ Real.log A) :
    ContinuousOn (fun x : ℝ =>
      (((Real.log x)^3-2*(Real.log x)^2-Real.log x-1) /
        ((Real.log x)^2-Real.log x-1)^2 -
        (1/Real.log x-1/(Real.log x)^2-1/(Real.log x)^4+4/(Real.log x)^5)))
      (Set.Ici A) := by
  intro x hx
  have hlogx := log_ge_of_mem_Ici hA hlog hx
  have hL : 0 < Real.log x := (show (0:ℝ) < 12 by norm_num).trans_le hlogx
  have hQ := quadratic_pos hlogx
  have hlogc : ContinuousAt Real.log x := Real.continuousAt_log (xpos_log_ne_zero hlogx)
  have hnum : ContinuousAt (fun t : ℝ => (Real.log t)^3-2*(Real.log t)^2-Real.log t-1) x :=
    (((hlogc.pow 3).sub (continuousAt_const.mul (hlogc.pow 2))).sub hlogc).sub continuousAt_const
  have hden : ContinuousAt (fun t : ℝ => (Real.log t)^2-Real.log t-1) x :=
    ((hlogc.pow 2).sub hlogc).sub continuousAt_const
  have hleft := hnum.div (hden.pow 2) (pow_ne_zero 2 hQ.ne')
  have hinvpow (k : ℕ) (a : ℝ) : ContinuousAt (fun t : ℝ => a/(Real.log t)^k) x :=
    continuousAt_const.div (hlogc.pow k) (pow_ne_zero k hL.ne')
  have hinv : ContinuousAt (fun t : ℝ => 1/Real.log t) x :=
    continuousAt_const.div hlogc hL.ne'
  have hright := (((hinv.sub (hinvpow 2 1)).sub (hinvpow 4 1)).add (hinvpow 5 4))
  exact (hleft.sub hright).continuousWithinAt

/-- The actual derivative is continuous on the range of partial summation. -/
theorem continuousOn_deriv_countComparison_sub_theta {A : ℝ}
    (hA : 2 ≤ A) (hlog : 12 ≤ Real.log A) :
    ContinuousOn (deriv (fun t : ℝ =>
      t/(Real.log t-1-1/Real.log t) - (t-t/(Real.log t)^3)/Real.log t)) (Set.Ici A) := by
  refine (continuousOn_countComparison_sub_theta_derivFormula hA hlog).congr ?_
  intro x hx
  exact (hasDerivAt_countComparison_sub_theta (log_ge_of_mem_Ici hA hlog hx)).deriv

/-- The derivative of the difference is bounded by the partial-summation integrand. -/
theorem deriv_countComparison_sub_theta_le {x : ℝ} (hx : 12 ≤ Real.log x) :
    deriv (fun t : ℝ =>
      t/(Real.log t-1-1/Real.log t) - (t-t/(Real.log t)^3)/Real.log t) x ≤
        1/(Real.log x)^2 - 1/(Real.log x)^5 := by
  let L := Real.log x
  have hL : 0 < L := (show (0:ℝ) < 12 by norm_num).trans_le hx
  have h4 : 0 ≤ 1/L^4 := by positivity
  have h5 : 0 ≤ 1/L^5 := by positivity
  have hbound := deriv_countComparison_le hx
  rw [(hasDerivAt_countComparison hx).deriv] at hbound
  rw [(hasDerivAt_countComparison_sub_theta hx).deriv]
  change (L^3-2*L^2-L-1)/(L^2-L-1)^2 - (1/L-1/L^2-1/L^4+4/L^5) ≤
    1/L^2-1/L^5
  change (L^3-2*L^2-L-1)/(L^2-L-1)^2 ≤ 1/L-3/L^4 at hbound
  have h5' : 4/L^5 = 4*(1/L^5) := by ring
  have h3' : 3/L^4 = 3*(1/L^4) := by ring
  rw [h3'] at hbound
  rw [h5']
  linarith only [hbound,h4,h5]

end OMA.FiroozbakhtPrimeCount

namespace OMA.FiroozbakhtCount

open Real MeasureTheory Set

theorem counting_from_theta {A x : ℝ} (hA : 2 ≤ A) (hlogA : 12 ≤ log A) (hx : A ≤ x)
    (hTheta : ∀ t ≥ A, |Chebyshev.theta t - t| ≤ t / log t ^ 3)
    (hAnchor : A / (log A - 1 - 1 / log A) + 2 * A / log A ^ 4 ≤
      (Nat.primeCounting ⌊A⌋₊ : ℝ))
    (rate : ℝ → ℝ) (rateCont : ContinuousOn rate (Ici A))
    (hRate : ∀ t ≥ A, HasDerivAt
      (fun t => t / (log t - 1 - 1 / log t) - ((t - t / log t ^ 3) / log t)) (rate t) t ∧
      rate t ≤ 1 / log t ^ 2 - 1 / log t ^ 5) :
    x / (log x - 1 - 1 / log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  let weight := fun t : ℝ => Chebyshev.theta t / (t * log t ^ 2)
  let target := fun t : ℝ => t / (log t - 1 - 1 / log t)
  let base := fun t : ℝ => (t - t / log t ^ 3) / log t
  have positive (t : ℝ) (ht : A ≤ t) : 0 < t ∧ 0 < log t := by
    have hAt := log_le_log (by linarith : 0 < A) ht
    exact ⟨by linarith, by linarith⟩
  have pointLo (t : ℝ) (ht : A ≤ t) : base t ≤ Chebyshev.theta t / log t := by
    have hl := (positive t ht).2
    have hb : t - t / log t ^ 3 ≤ Chebyshev.theta t := by
      linarith only [(abs_le.mp (hTheta t ht)).1]
    exact div_le_div_of_nonneg_right hb hl.le
  have pointHi : Chebyshev.theta A / log A ≤ A / log A + A / log A ^ 4 := by
    have hl := (positive A le_rfl).2
    have hb : Chebyshev.theta A ≤ A + A / log A ^ 3 := by
      linarith only [(abs_le.mp (hTheta A le_rfl)).2]
    calc
      _ ≤ (A + A / log A ^ 3) / log A := div_le_div_of_nonneg_right hb hl.le
      _ = _ := by field_simp [hl.ne']
  have integrableStart (t : ℝ) (ht : 2 ≤ t) : IntervalIntegrable weight volume 2 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht).2
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq t)
  have intTail : IntervalIntegrable weight volume A x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).2
      ((Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
        (Icc_subset_Icc_left hA))
  have subInterval : Icc A x ⊆ Ici A := by
    intro t ht
    exact ht.1
  have intRate : IntervalIntegrable rate volume A x :=
    (rateCont.mono subInterval).intervalIntegrable_of_Icc hx
  have rateBound (t : ℝ) (ht : t ∈ Icc A x) : rate t ≤ weight t := by
    have ⟨hp, hl⟩ := positive t ht.1
    have htheta : t - t / log t ^ 3 ≤ Chebyshev.theta t := by
      linarith only [(abs_le.mp (hTheta t ht.1)).1]
    calc
      rate t ≤ 1 / log t ^ 2 - 1 / log t ^ 5 := (hRate t ht.1).2
      _ = (t - t / log t ^ 3) / (t * log t ^ 2) := by
        field_simp [hp.ne', hl.ne']
      _ ≤ weight t := div_le_div_of_nonneg_right htheta
        (mul_nonneg hp.le (sq_nonneg (log t)))
  have integralRate : (∫ t in A..x, rate t) = target x - base x - (target A - base A) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ intRate
    intro t ht
    rw [uIcc_of_le hx] at ht
    exact (hRate t ht.1).1
  have integralBound := intervalIntegral.integral_mono_on hx intRate intTail rateBound
  rw [integralRate] at integralBound
  have split := intervalIntegral.integral_add_adjacent_intervals
    (integrableStart A hA) intTail
  have piA := Chebyshev.primeCounting_eq_theta_div_log_add_integral hA
  have piX := Chebyshev.primeCounting_eq_theta_div_log_add_integral (hA.trans hx)
  change (Nat.primeCounting ⌊A⌋₊ : ℝ) = Chebyshev.theta A / log A +
    (∫ t in 2..A, weight t) at piA
  change (Nat.primeCounting ⌊x⌋₊ : ℝ) = Chebyshev.theta x / log x +
    (∫ t in 2..x, weight t) at piX
  change target A + 2 * A / log A ^ 4 ≤ _ at hAnchor
  have anchorBridge : target A - base A ≤ (∫ t in 2..A, weight t) := by
    have eq : base A = A / log A - A / log A ^ 4 := by
      dsimp only [base]
      field_simp [(positive A le_rfl).2.ne']
    have twice : 2 * A / log A ^ 4 = 2 * (A / log A ^ 4) := by ring
    rw [eq]
    rw [twice] at hAnchor
    linarith only [hAnchor, piA, pointHi]
  change target x ≤ _
  linarith only [piX, split, integralBound, anchorBridge, pointLo x hx]

end OMA.FiroozbakhtCount

namespace OMA.FiroozbakhtCount

open Real

theorem finite_from_integer {p h : ℕ} (hpos : 0 < h) (cutoff : 2 ^ h ≤ p ^ 256)
    (certificate :
      let u := 693147 * h
      let v := 256000000
      p * u * v + p.primeCounting * (u * v + v ^ 2) ≤ p.primeCounting * u ^ 2) :
    (p : ℝ) ≤ (p.primeCounting : ℝ) * (log p - 1 - 1 / log p) := by
  let u := 693147 * h
  let v : ℕ := 256000000
  change p * u * v + p.primeCounting * (u * v + v ^ 2) ≤ p.primeCounting * u ^ 2 at certificate
  have hu : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos (by decide) hpos)
  have hv : (0 : ℝ) < (v : ℝ) := by norm_num [v]
  have cutoffReal : (2 : ℝ) ^ h ≤ (p : ℝ) ^ 256 := by
    exact_mod_cast cutoff
  have logs := log_le_log (by positivity) cutoffReal
  simp only [log_pow, Nat.cast_ofNat] at logs
  have coarse : (693147 / 1000000 : ℝ) ≤ log 2 :=
    (by norm_num : (693147 / 1000000 : ℝ) < 0.6931471803).le.trans log_two_gt_d9.le
  have ellLower : (u : ℝ) / (v : ℝ) ≤ log p := by
    have hScaled := mul_le_mul_of_nonneg_left coarse (Nat.cast_nonneg h)
    dsimp only [u, v]
    push_cast
    linarith only [logs, hScaled]
  have ellPositive := div_pos hu hv
  have coeffLe : (u : ℝ) / (v : ℝ) - 1 - 1 / ((u : ℝ) / (v : ℝ)) ≤
      log p - 1 - 1 / log p := by
    exact sub_le_sub (sub_le_sub_right ellLower 1)
      (one_div_le_one_div_of_le ellPositive ellLower)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left coeffLe (Nat.cast_nonneg _))
  have certReal : (p : ℝ) * (u : ℝ) * (v : ℝ) +
      (p.primeCounting : ℝ) * ((u : ℝ) * (v : ℝ) + (v : ℝ) ^ 2) ≤
      (p.primeCounting : ℝ) * (u : ℝ) ^ 2 := by
    exact_mod_cast certificate
  apply (mul_le_mul_iff_left₀ (mul_pos hu hv)).mp
  have algebra :
      (p.primeCounting : ℝ) * ((u : ℝ) / (v : ℝ) - 1 - 1 / ((u : ℝ) / (v : ℝ))) *
          ((u : ℝ) * (v : ℝ)) =
        (p.primeCounting : ℝ) * ((u : ℝ) ^ 2 - ((u : ℝ) * (v : ℝ) + (v : ℝ) ^ 2)) := by
    field_simp [hu.ne', hv.ne']
    ring
  rw [algebra, mul_sub]
  linarith only [certReal]

theorem log_anchor_lower : (18.3142 : ℝ) ≤ log 90000000 := by
  have nn : (2 : ℕ) ^ 1691 ≤ (90000000 : ℕ) ^ 64 := by
    rw [show (1691 : ℕ) = 256 * 6 + 155 by decide, pow_add, pow_mul]
    norm_num
  have rr : (2 : ℝ) ^ 1691 ≤ (90000000 : ℝ) ^ 64 := by exact_mod_cast nn
  have logs := log_le_log (by positivity) rr
  simp only [log_pow, Nat.cast_ofNat] at logs
  linarith only [logs, log_two_gt_d9]

theorem anchor_from_count (hcount : 5216100 ≤ Nat.primeCounting 90000000) :
    (90000000 : ℝ) / (log 90000000 - 1 - 1 / log 90000000) +
      2 * 90000000 / log 90000000 ^ 4 ≤ (Nat.primeCounting 90000000 : ℝ) := by
  let b : ℝ := 18.3142
  let L := log (90000000 : ℝ)
  have hb : 0 < b := by norm_num [b]
  have hbl : b ≤ L := log_anchor_lower
  have hden : 0 < b - 1 - 1 / b := by norm_num [b]
  have denComp : b - 1 - 1 / b ≤ L - 1 - 1 / L := by
    exact sub_le_sub (sub_le_sub_right hbl 1) (one_div_le_one_div_of_le hb hbl)
  have powComp : b ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hb.le hbl _
  have a := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 90000000) hden denComp
  have e := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2 * 90000000)
    (pow_pos hb 4) powComp
  have v : (90000000 : ℝ) / (b - 1 - 1 / b) + 2 * 90000000 / b ^ 4 ≤ 5216100 := by
    norm_num [b]
  have h : (5216100 : ℝ) ≤ (Nat.primeCounting 90000000 : ℝ) := by exact_mod_cast hcount
  change (90000000 : ℝ) / (L - 1 - 1 / L) + 2 * 90000000 / L ^ 4 ≤ _
  exact (add_le_add a e).trans (v.trans h)

end OMA.FiroozbakhtCount

namespace OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1

open Real OMA.FiroozbakhtCount OMA.FiroozbakhtPrimeCount

/-- The k = 3, eta = 1 case of Dusart's explicit two-sided theta estimate. -/
def H1 : Prop := ∀ x : ℝ, 90000000 ≤ x →
  |Chebyshev.theta x - x| ≤ x / log x ^ 3

/-- A finite integer check with each logarithm rounded down using binary bit length. -/
def H2 : Prop := ∀ p : ℕ, 1772201 ≤ p → p < 90000000 → p.Prime →
  ∃ h : ℕ, 0 < h ∧ 2 ^ h ≤ p ^ 256 ∧
    let u := 693147 * h
    let v := 256000000
    p * u * v + p.primeCounting * (u * v + v ^ 2) ≤ p.primeCounting * u ^ 2

/-- A single lower count at the anchor of the integral comparison. -/
def H3 : Prop := 5216100 ≤ Nat.primeCounting 90000000

theorem main : H1 → H2 → H3 →
    OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1.H1 := by
  intro hTheta hFinite hAnchor p hmin hp
  by_cases hsmall : p < 90000000
  · obtain ⟨h, hpos, hpower, certificate⟩ := hFinite p hmin hsmall hp
    exact finite_from_integer hpos hpower certificate
  · have hA : (2 : ℝ) ≤ 90000000 := by norm_num
    have hLogA : (12 : ℝ) ≤ log 90000000 := (by norm_num : (12 : ℝ) ≤ 18.3142).trans log_anchor_lower
    have hLarge : (90000000 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.le_of_not_lt hsmall)
    have logLarge (t : ℝ) (ht : (90000000 : ℝ) ≤ t) : 12 ≤ log t :=
      hLogA.trans (log_le_log (by norm_num) ht)
    have anchor : (90000000 : ℝ) / (log 90000000 - 1 - 1 / log 90000000) +
        2 * 90000000 / log 90000000 ^ 4 ≤
          (Nat.primeCounting ⌊(90000000 : ℝ)⌋₊ : ℝ) := by
      rw [show ⌊(90000000 : ℝ)⌋₊ = 90000000 by norm_num]
      exact anchor_from_count hAnchor
    let rate := deriv (fun t : ℝ => t / (log t - 1 - 1 / log t) -
      (t - t / log t ^ 3) / log t)
    have hRate (t : ℝ) (ht : (90000000 : ℝ) ≤ t) :
        HasDerivAt (fun t : ℝ => t / (log t - 1 - 1 / log t) -
          (t - t / log t ^ 3) / log t) (rate t) t ∧
        rate t ≤ 1 / log t ^ 2 - 1 / log t ^ 5 := by
      have h := hasDerivAt_countComparison_sub_theta (logLarge t ht)
      exact ⟨by simpa only [rate, h.deriv] using h,
        deriv_countComparison_sub_theta_le (logLarge t ht)⟩
    have count := counting_from_theta hA hLogA hLarge hTheta anchor rate
      (continuousOn_deriv_countComparison_sub_theta hA hLogA) hRate
    rw [Nat.floor_natCast] at count
    have hLogP := logLarge p hLarge
    have invLe : 1 / log p ≤ (1 : ℝ) := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (by linarith : (1 : ℝ) ≤ log p)
    exact (div_le_iff₀ (by linarith : 0 < log p - 1 - 1 / log p)).mp count

end OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1
