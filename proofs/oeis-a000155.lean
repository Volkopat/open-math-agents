import OMAStatements.S_oeis_a000155

-- Credit: @rleshner (agent: Codex, model: GPT-6)

/-!
# Yanev's integral formula for the nearest integer to Kₙ(1)

Velin Yanev conjectured the Chebyshev integral formula in OEIS A000155.
Mark van Hoeij's 2011 Maple generating series in the entry gives the same
candidate integers. Formally integrating the generating function of the
Chebyshev polynomials term by term gives that series because the exponential
moments are factorials. The statement's Lean formalization is due to @Dugongue.

Write Iₙ for the integer obtained from the Chebyshev integral. Substituting
x = cosh(t) in the part above 1 gives Kₙ(1) − Iₙ as the difference of a
positive tail and an integral on [0,1]. Integration by parts using
Tₙ′ = n Uₙ₋₁ controls the latter for n ≥ 5. Four explicit low-degree
integrals and a lower estimate on [0, log 2] handle n = 1, 2, 3, 4.
-/

open MeasureTheory OMA.S_oeis_a000155
namespace A000155Integral

private noncomputable def moment (k : ℕ) (x : ℝ) : ℝ := Real.exp (-x) * x^k

private noncomputable def weighted (j k : ℕ) (x : ℝ) : ℝ := moment k x * chebyshevU j x

private def HasIntMoment (f : ℝ → ℝ) : Prop :=
  IntegrableOn f (Set.Ioi 0) ∧ ∃ z : ℤ, (z : ℝ) = ∫ x in Set.Ioi (0:ℝ), f x

private theorem baseMoment (k : ℕ) : HasIntMoment (moment k) := by
  have hp : (0:ℝ) < (k:ℝ)+1 := by positivity
  constructor
  · unfold moment
    simpa [Real.rpow_natCast] using Real.GammaIntegral_convergent hp
  · refine ⟨(k.factorial:ℤ), ?_⟩
    have h := (Real.Gamma_nat_eq_factorial k).symm.trans (Real.Gamma_eq_integral hp)
    simpa [moment, Real.rpow_natCast] using h

private theorem scaleMoment (f : ℝ → ℝ) (hf : HasIntMoment f) :
    HasIntMoment (fun x => 2 * f x) := by
  obtain ⟨hi,z,hz⟩ := hf
  refine ⟨hi.const_mul 2, 2*z, ?_⟩
  rw [MeasureTheory.integral_const_mul, ← hz]
  push_cast
  rfl

private theorem subMoment (f g : ℝ → ℝ) (hf : HasIntMoment f) (hg : HasIntMoment g) :
    HasIntMoment (fun x => f x - g x) := by
  obtain ⟨hi,z,hz⟩ := hf
  obtain ⟨hj,w,hw⟩ := hg
  refine ⟨hi.sub hj, z-w, ?_⟩
  rw [MeasureTheory.integral_sub hi hj, ← hz, ← hw, Int.cast_sub]

private theorem weighted_integral (j k : ℕ) : HasIntMoment (weighted j k) := by
  induction j using Nat.twoStepInduction generalizing k with
  | zero =>
    have h : weighted 0 k = moment k := by funext x; simp [weighted,chebyshevU]
    rw [h]; exact baseMoment _
  | one =>
    have h : weighted 1 k = fun x => 2 * moment (k+1) x := by
      funext x; simp [weighted, moment, chebyshevU, pow_succ]; ring
    rw [h]; exact scaleMoment _ (baseMoment _)
  | more j h0 h1 =>
    have h : weighted (j+2) k = fun x => 2 * weighted (j+1) (k+1) x - weighted j k x := by
      funext x; simp [weighted, moment, chebyshevU, pow_succ]; ring
    rw [h]; exact subMoment _ _ (scaleMoment _ (h1 _)) (h0 _)

private theorem at_zero (j : ℕ) :
    (fun x : ℝ => chebyshevU j x / Real.exp x) = weighted j 0 := by
  funext x; simp [weighted, moment, Real.exp_neg, div_eq_mul_inv, mul_comm]

theorem integrable_U (j : ℕ) :
    IntegrableOn (fun x : ℝ => chebyshevU j x / Real.exp x) (Set.Ioi 0) := by
  rw [at_zero]; exact (weighted_integral j 0).1

theorem integral_int (n : ℕ) : ∃ k : ℤ, (k:ℝ) =
    ∫ x in Set.Ioi (0:ℝ), chebyshevU (n-1) x / Real.exp x := by
  change ∃ k : ℤ, (k:ℝ) = ∫ x in Set.Ioi (0:ℝ), (fun x => chebyshevU (n-1) x / Real.exp x) x
  rw [at_zero]
  exact (weighted_integral _ _).2
end A000155Integral

open MeasureTheory Set Real
open OMA.S_oeis_a000155

namespace A000155Analytic

/-- The auxiliary positive remainder left after replacing cosh(nt) by sinh(nt). -/
noncomputable def B (n : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), exp (-cosh t) * exp (-((n : ℝ)*t))

theorem B_integrable (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (fun t : ℝ => exp (-cosh t) * exp (-((n : ℝ)*t))) (Ioi (0 : ℝ)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (exp_neg_integrableOn_Ioi 0 hpos).mono' (by fun_prop)
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), neg_mul]
  exact mul_le_of_le_one_left (exp_pos _).le (exp_le_one_iff.mpr (by linarith [cosh_pos t]))

/-- Match the recurrence used in the statement with Mathlib's polynomials. -/
theorem poly_U (n : ℕ) (x : ℝ) :
    chebyshevU n x = (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [chebyshevU, Polynomial.Chebyshev.U_zero]
  | one => simp [chebyshevU, Polynomial.Chebyshev.U_one]
  | more n h0 h1 =>
    simp only [chebyshevU, Nat.cast_add, Nat.cast_ofNat, Polynomial.Chebyshev.U_add_two,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    rw [h0, h1]; push_cast; rfl

private theorem cosh_image : cosh '' Ioi (0 : ℝ) = Ioi 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact one_lt_cosh.mpr (ne_of_gt ht)
  · intro hx
    exact ⟨arcosh x, arcosh_pos hx, cosh_arcosh (le_of_lt hx)⟩

/-- The Bessel remainder after the change of variable x = cosh(t). -/
theorem bridge_from_integrability (n : ℕ) (hn : 1 ≤ n)
    (hint : IntegrableOn (fun x : ℝ => chebyshevU (n-1) x / exp x) (Ioi (0 : ℝ))) :
    besselK1 n - (∫ x in Ioi (0 : ℝ), chebyshevU (n-1) x / exp x) =
      B n - (∫ x in (0 : ℝ)..1, chebyshevU (n-1) x / exp x) := by
  let f := fun x : ℝ => chebyshevU (n-1) x / exp x
  let F := fun t : ℝ => exp (-cosh t) * sinh ((n:ℝ)*t)
  have iden (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) : |sinh t| • f (cosh t) = F t := by
    have h := Polynomial.Chebyshev.U_real_cosh t ((n-1 : ℕ) : ℤ)
    have hc : (((n-1:ℕ):ℤ):ℝ)+1 = (n:ℝ) := by norm_cast; omega
    rw [hc] at h
    simp only [f, F, smul_eq_mul, abs_of_nonneg (sinh_nonneg_iff.mpr (le_of_lt ht)),
      div_eq_mul_inv, poly_U, exp_neg]
    linear_combination (exp (cosh t))⁻¹ * h
  have inj := cosh_injOn.mono (Ioi_subset_Ici_self (a := (0 : ℝ)))
  have hder (x : ℝ) (_ : x ∈ Ioi (0:ℝ)) := (hasDerivAt_cosh x).hasDerivWithinAt (s := Ioi (0:ℝ))
  have hI : IntegrableOn f (Ioi (1:ℝ)) := hint.mono_set (Ioi_subset_Ioi (by norm_num))
  have hint' := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder inj f
  rw [cosh_image] at hint'
  have hF : IntegrableOn F (Ioi (0:ℝ)) := (hint'.mp hI).congr_fun iden measurableSet_Ioi
  have hJ := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder inj f
  rw [cosh_image] at hJ
  have hJ' : (∫ x in Ioi (1:ℝ), f x) = ∫ t in Ioi (0:ℝ), F t :=
    hJ.trans (setIntegral_congr_fun measurableSet_Ioi iden)
  have hK : besselK1 n = (∫ t in Ioi (0:ℝ), F t) + B n := by
    unfold besselK1 B
    rw [← integral_add hF (B_integrable n hn)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only [F]
    rw [← cosh_sub_sinh ((n:ℝ)*t)]
    ring
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint hI
  change (∫ x in (0:ℝ)..1, f x) + (∫ x in Ioi (1:ℝ), f x) = ∫ x in Ioi (0:ℝ), f x at hsplit
  change besselK1 n - (∫ x in Ioi (0:ℝ), f x) = B n - (∫ x in (0:ℝ)..1, f x)
  linarith

end A000155Analytic

open MeasureTheory Set Real

namespace A000155Analytic

theorem B_nonneg (n : ℕ) : 0 ≤ B n :=
  integral_nonneg (fun _ => mul_nonneg (exp_pos _).le (exp_pos _).le)

/-- Majorizing exp(-cosh t) by exp(-1) leaves an elementary exponential integral. -/
theorem B_upper (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) * B n ≤ exp (-1) := by
  have hpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htail : IntegrableOn (fun t : ℝ => exp (-((n : ℝ)*t))) (Ioi (0:ℝ)) := by
    simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hpos
  have hle : B n ≤ ∫ t in Ioi (0:ℝ), exp (-1) * exp (-((n:ℝ)*t)) := by
    apply integral_mono (B_integrable n hn) (htail.const_mul _)
    intro t
    exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith [one_le_cosh t])) (exp_pos _).le
  rw [integral_const_mul] at hle
  have hval : (∫ t in Ioi (0:ℝ), exp (-((n:ℝ)*t))) = 1/(n:ℝ) := by
    simpa [neg_mul] using integral_exp_mul_Ioi (a := -(n:ℝ)) (by linarith : -(n:ℝ) < 0) 0
  rw [hval, ← div_eq_mul_one_div] at hle
  linarith [(le_div_iff₀ hpos).mp hle]

end A000155Analytic

open MeasureTheory Set Real
namespace A000155Analytic

private theorem weight_lb (t : ℝ) (ht : t ∈ Icc 0 (log 2)) :
    2/7 ≤ exp (-cosh t) := by
  have hlog : 0 ≤ log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hcos : cosh t ≤ 5/4 := calc
    cosh t ≤ cosh (log 2) := cosh_strictMonoOn.monotoneOn ht.1 hlog ht.2
    _ = 5/4 := by rw [cosh_eq,exp_log (by norm_num),exp_neg,exp_log (by norm_num)]; norm_num
  have ex : exp (5/4 : ℝ) ≤ 7/2 := by
    have pow_eq : exp (5/4 : ℝ)^4 = exp (1:ℝ)^5 := by
      rw [←exp_nat_mul,←exp_nat_mul]; norm_num
    have h := pow_le_pow_left₀ (exp_pos 1).le (le_of_lt exp_one_lt_d9) 5
    by_contra! bad
    have q := pow_lt_pow_left₀ bad (by norm_num : (0:ℝ) ≤ 7/2) (by norm_num : (4:ℕ) ≠ 0)
    rw [pow_eq] at q
    norm_num at h q
    linarith
  rw [exp_neg]
  apply (le_inv_comm₀ (by norm_num) (exp_pos _)).mpr
  norm_num
  exact (exp_le_exp.mpr hcos).trans ex

private theorem lo_from_strip (n : ℕ) (hn : 1 ≤ n) (r : ℝ)
    (hr : ∀ t ∈ Icc 0 (log 2), r * exp (-t) ≤ exp (-cosh t) * exp (-((n:ℝ)*t))) :
    r/2 ≤ B n := by
  let f : ℝ → ℝ := fun t => exp (-cosh t) * exp (-((n:ℝ)*t))
  have hlog : 0 ≤ log (2:ℝ) := Real.log_nonneg (by norm_num)
  have ha : (∫ t in (0:ℝ)..log 2, exp (-t)) = 1/2 := by
    have hD (x : ℝ) : HasDerivAt (fun y : ℝ => -exp (-y)) (exp (-x)) x := by
      have e : HasDerivAt (fun y : ℝ => exp (-y)) (-exp (-x)) x := by
        simpa using (hasDerivAt_id x).neg.exp
      have he := e.const_mul (-1 : ℝ)
      simpa only [neg_mul,one_mul,neg_neg] using he
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hD x) (Continuous.intervalIntegrable (by fun_prop) _ _),exp_neg,exp_log (by norm_num)]
    norm_num
  have k : r/2 = ∫ t in (0:ℝ)..log 2, r*exp (-t) := by
    rw [intervalIntegral.integral_const_mul,ha]; ring
  rw [k]
  calc
    _ ≤ ∫ t in (0:ℝ)..log 2, f t :=
      intervalIntegral.integral_mono_on hlog (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by dsimp [f]; fun_prop) _ _) hr
    _ ≤ B n := by
      rw [intervalIntegral.integral_of_le hlog]
      exact setIntegral_mono_set (B_integrable n hn) (.of_forall (fun x => by dsimp [f]; positivity))
        (.of_forall (fun x h => h.1))

theorem B_one_lower : 1/7 ≤ B 1 := by
  rw [show (1/7:ℝ) = (2/7)/2 by norm_num]
  apply lo_from_strip 1 (by norm_num)
  intro t ht
  simp only [Nat.cast_one,one_mul]
  exact mul_le_mul_of_nonneg_right (weight_lb t ht) (exp_pos _).le

theorem B_two_lower : 1/14 ≤ B 2 := by
  rw [show (1/14:ℝ) = (1/7)/2 by norm_num]
  apply lo_from_strip 2 (by norm_num)
  intro t ht
  have h : 1/2 ≤ exp (-t) := calc
    1/2 = exp (-log 2) := by rw [exp_neg,exp_log (by norm_num)]; norm_num
    _ ≤ _ := exp_le_exp.mpr (neg_le_neg ht.2)
  have z := mul_le_mul (weight_lb t ht) h (by norm_num) (exp_pos _).le
  have q := mul_le_mul_of_nonneg_right z (exp_pos (-t)).le
  rw [Nat.cast_ofNat,show -(2*t) = -t + -t by ring,exp_add]
  nlinarith only [q]

end A000155Analytic

open MeasureTheory Set Real Polynomial
open Polynomial.Chebyshev OMA.S_oeis_a000155

namespace A000155Bounds

private noncomputable abbrev low (n : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..1, chebyshevU (n-1) x / exp x

private lemma abs_T (n : ℕ) {x : ℝ} (h : x ∈ Icc (0:ℝ) 1) : |(T ℝ n).eval x| ≤ 1 := by
  have hx : -1 ≤ x := by linarith [h.1]
  rw [← Real.cos_arccos hx h.2, T_real_cos]
  exact Real.abs_cos_le_one _

private lemma exp_neg_deriv (x : ℝ) : HasDerivAt (fun y : ℝ => exp (-y)) (-exp (-x)) x := by
  simpa using ((hasDerivAt_id x).neg.exp)

private lemma expansion (poly_U : ∀ j : ℕ, ∀ x : ℝ, chebyshevU j x = (U ℝ j).eval x)
    (n : ℕ) (hn : 0 < n) :
    (n:ℝ) * low n = exp (-1) - (T ℝ n).eval 0 +
      ∫ x in (0:ℝ)..1, (T ℝ n).eval x * exp (-x) := by
  let P := T ℝ (n:ℤ)
  have dh (x : ℝ) : HasDerivAt (fun s => P.eval s) ((n:ℝ)*chebyshevU (n-1) x) x := by
    rw [poly_U, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    have hd := P.hasDerivAt x
    simpa only [P, T_derivative_eq_U, Polynomial.eval_mul, Polynomial.eval_intCast, Int.cast_natCast, Polynomial.eval_natCast] using hd
  have du : Continuous (fun x : ℝ => (n:ℝ)*chebyshevU (n-1) x) := by
    simp_rw [poly_U]
    fun_prop
  have de (x : ℝ) : HasDerivAt (fun s : ℝ => exp (-s)) (-exp (-x)) x := by
    exact exp_neg_deriv x
  have hh := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b:=1) P.continuous.continuousOn (by fun_prop)
    (fun x _ => dh x) (fun x _ => de x) (du.intervalIntegrable ..)
    (Continuous.intervalIntegrable (u:=fun x : ℝ => -exp (-x)) (by fun_prop) ..)
  rw [intervalIntegral.integral_add] at hh
  · simp only [mul_neg, intervalIntegral.integral_neg, neg_zero, exp_zero, mul_one, P, T_eval_one,
      one_mul] at hh
    have fac : (∫ x in (0:ℝ)..1, (n:ℝ)*chebyshevU (n-1) x * exp (-x)) = (n:ℝ)*low n := by
      simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
      simp [low, div_eq_mul_inv, exp_neg]
    rw [fac] at hh
    linarith
  · exact (du.mul (by fun_prop)).intervalIntegrable ..
  · exact (P.continuous.mul (by fun_prop)).intervalIntegrable ..

private lemma weighted (n : ℕ) : |∫ x in (0:ℝ)..1, (T ℝ n).eval x * exp (-x)| ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (C := (1:ℝ)) (f := fun x : ℝ => (T ℝ n).eval x * exp (-x)) (by
      intro x hx
      rw [Set.uIoc_of_le (by norm_num)] at hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
      exact mul_le_one₀ (abs_T n ⟨hx.1.le,hx.2⟩) (exp_pos _).le
        (Real.exp_le_one_iff.mpr (by linarith [hx.1])))
  simpa using h

private lemma e_inv_bound : (3678:ℝ)/10000 < exp (-1) ∧ exp (-1) < 3679/10000 := by
  rw [Real.exp_neg]
  constructor
  · rw [lt_inv_comm₀ (by norm_num) (exp_pos _)]
    norm_num
    linarith [Real.exp_one_lt_d9]
  · rw [inv_lt_comm₀ (exp_pos _) (by norm_num)]
    norm_num
    linarith [Real.exp_one_gt_d9]

private lemma small_eval (k : ℕ) (p : ℝ[X])
    (h : ∀ x : ℝ, p.eval x - p.derivative.eval x = chebyshevU (k-1) x) :
    low k = p.eval 0 - p.eval 1 * exp (-1) := by
  have dh (x : ℝ) : HasDerivAt (fun y : ℝ => -(p.eval y * exp (-y)))
      (chebyshevU (k-1) x / exp x) x := by
    have hd := ((p.hasDerivAt x).mul (exp_neg_deriv x)).neg
    have hv : chebyshevU (k-1) x / exp x =
        -(p.derivative.eval x * exp (-x) + p.eval x * (-exp (-x))) := by
      rw [← h, div_eq_mul_inv, ← Real.exp_neg]; ring
    rw [hv]
    exact hd
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b:=1) (fun x _ => dh x)
  have HC : Continuous (fun x : ℝ => chebyshevU (k-1) x / exp x) := by
    simp_rw [← h]
    exact (p.continuous.sub p.derivative.continuous).div Real.continuous_exp (fun x => (exp_pos x).ne')
  have H := hh (HC.intervalIntegrable ..)
  simpa [low, sub_eq_add_neg, add_comm] using H

private lemma low_values : low 1 = 1 - exp (-1) ∧ low 2 = 2 - 4*exp (-1) ∧
    low 3 = 7 - 19*exp (-1) ∧ low 4 = 44 - 120*exp (-1) := by
  have h1 := small_eval 1 1 (by intro x; norm_num [chebyshevU])
  have h2 := small_eval 2 (2*X+2) (by intro x; norm_num [chebyshevU])
  have h3 := small_eval 3 (4*X^2+8*X+7) (by intro x; norm_num [chebyshevU]; ring)
  have h4 := small_eval 4 (8*X^3+24*X^2+44*X+44) (by intro x; norm_num [chebyshevU]; ring)
  norm_num at h1 h2 h3 h4
  exact ⟨h1,h2,h3,h4⟩

theorem close (poly_U : ∀ j : ℕ, ∀ x : ℝ, chebyshevU j x = (U ℝ j).eval x)
    (b : ℕ → ℝ) (bpos : ∀ n, 0 ≤ b n)
    (bupper : ∀ n : ℕ, 1 ≤ n → (n:ℝ)*b n ≤ exp (-1))
    (b1 : (1:ℝ)/7 ≤ b 1) (b2 : (1:ℝ)/14 ≤ b 2)
    (n : ℕ) (hn : 1 ≤ n) :
    |b n - (∫ x in (0:ℝ)..1, chebyshevU (n-1) x / exp x)| < 1/2 := by
  change |b n - low n| < 1/2
  obtain ⟨he₁, he₂⟩ := e_inv_bound
  have b₀ := bpos n
  have b₃ := bupper n hn
  by_cases hn' : n ≤ 4
  · obtain ⟨l₁,l₂,l₃,l₄⟩ := low_values
    interval_cases n <;> norm_num at b₃ <;> rw [abs_lt] <;> constructor <;> linarith
  · have hn₅ : (5:ℝ) ≤ n := by exact_mod_cast (show 5 ≤ n by omega)
    have heq := expansion poly_U n (by omega)
    obtain ⟨hw₁,hw₂⟩ := abs_le.mp (weighted n)
    obtain ⟨ht₁,ht₂⟩ := abs_le.mp (abs_T n (x:=0) (by constructor <;> norm_num))
    have hmul : (-(n:ℝ)/2) < (n:ℝ)*(b n-low n) ∧ (n:ℝ)*(b n-low n) < (n:ℝ)/2 := by
      constructor <;> nlinarith [mul_nonneg (show 0 ≤ (n:ℝ) by positivity) b₀]
    rw [abs_lt]
    constructor
    · exact (lt_of_mul_lt_mul_left (a := (n:ℝ)) (b := -(1/2)) (c := b n - low n)
        (by linarith [hmul.1]) (by positivity))
    · exact (lt_of_mul_lt_mul_left (a := (n:ℝ)) (b := b n - low n) (c := 1/2)
        (by linarith [hmul.2]) (by positivity))

end A000155Bounds

theorem OMA.solution : type_of% @OMA.S_oeis_a000155.main := by
  intro n hn
  obtain ⟨k,hk⟩ := A000155Integral.integral_int n
  have h := A000155Bounds.close A000155Analytic.poly_U A000155Analytic.B
    A000155Analytic.B_nonneg A000155Analytic.B_upper
    A000155Analytic.B_one_lower A000155Analytic.B_two_lower n hn
  have hb := A000155Analytic.bridge_from_integrability n hn (A000155Integral.integrable_U (n-1))
  rw [← hb, ← hk] at h
  obtain ⟨h₁,h₂⟩ := abs_lt.mp h
  have hr : round (OMA.S_oeis_a000155.besselK1 n) = k := round_eq_iff.mpr
    ⟨by linarith, by linarith⟩
  rw [hr]
  exact hk
