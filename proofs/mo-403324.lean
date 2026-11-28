import OMAStatements.S_mo_403324

/-!
This proves Margaret Kail's binomial–beta inequality (MathOverflow 403324).
The normalized beta tail gives a density on [0,1]. Its log-concave survival
allows comparison of two convex moments with the exponential law of equal mean.
The binomial entropy estimate and weighted Cauchy–Schwarz give the requested bound.
-/

section
open MeasureTheory ProbabilityTheory Polynomial Finset
open scoped Polynomial
noncomputable section
namespace BetaNormalization

def weighted (n : ℕ) (f : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ range (n+1), C (f j) * bernsteinPolynomial ℝ n j

theorem derivative_weighted (n : ℕ) (f : ℕ → ℝ) :
    (weighted (n+1) f).derivative =
      (n+1 : ℕ) * weighted n (fun j => f (j+1)-f j) := by
  unfold weighted
  rw [Polynomial.derivative_sum, Finset.sum_range_succ', Finset.mul_sum]
  simp only [derivative_C_mul, bernsteinPolynomial.derivative_succ,
    bernsteinPolynomial.derivative_zero, Nat.add_sub_cancel, map_sub]
  let B := bernsteinPolynomial ℝ n
  have hlast : B (n+1) = 0 := bernsteinPolynomial.eq_zero_of_lt ℝ (by omega)
  change (∑ x ∈ range (n+1), C (f (x+1))*((n+1:ℕ)*(B x-B (x+1)))) +
    C (f 0)*(-((n+1:ℕ):ℝ[X])*B 0) = _
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
  have h : (∑ x ∈ range (n+1), C (f (x+1))*(((n+1:ℕ):ℝ[X])*B (x+1))) +
      C (f 0)*(((n+1:ℕ):ℝ[X])*B 0) =
      ∑ x ∈ range (n+1), C (f x)*(((n+1:ℕ):ℝ[X])*B x) := by
    rw [← Finset.sum_range_succ' (fun x => C (f x)*(((n+1:ℕ):ℝ[X])*B x)), Finset.sum_range_succ]
    simp [hlast]
  simp only [← mul_assoc] at h ⊢
  unfold B at h ⊢
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← mul_assoc, mul_comm ((n+1:ℕ):ℝ[X]) (C _)]
  linear_combination -h

def excess (n k : ℕ) := weighted n (fun j => (↑(j-k) : ℝ))
def tail (n k : ℕ) := weighted n (fun j => if k ≤ j then 1 else 0)

theorem derivative_excess (n k : ℕ) :
    (excess (n+1) k).derivative = (n+1:ℕ) * tail n k := by
  rw [excess, derivative_weighted, tail]
  congr 2
  funext j
  split_ifs with h
  · have he : j+1-k = (j-k)+1 := by omega
    simp [he]
  · simp [Nat.sub_eq_zero_of_le (show j+1≤k by omega), Nat.sub_eq_zero_of_le (by omega : j≤k)]

theorem derivative_tail (n k : ℕ) (hk : k ≤ n) :
    (tail (n+1) (k+1)).derivative = (n+1:ℕ) * bernsteinPolynomial ℝ n k := by
  rw [tail, derivative_weighted, weighted]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · simp [show ¬k+1≤b+1 by omega, show ¬k+1≤b by omega]
    · simp [show k+1≤b+1 by omega, show k+1≤b by omega]
  · simp [show k<n+1 by omega]

theorem eval_zero_weighted (n : ℕ) (f : ℕ → ℝ) : (weighted n f).eval 0 = f 0 := by
  simp [weighted, Polynomial.eval_finsetSum, bernsteinPolynomial.eval_at_0]

theorem eval_one_weighted (n : ℕ) (f : ℕ → ℝ) : (weighted n f).eval 1 = f n := by
  simp [weighted, Polynomial.eval_finsetSum, bernsteinPolynomial.eval_at_1]

theorem expectedExcess_eq (n k : ℕ) (p : Set.Icc (0:ℝ) 1) :
    OMA.S_mo_403324.expectedExcess n k p = (excess n k).eval (p:ℝ) := by
  simp [OMA.S_mo_403324.expectedExcess, excess, weighted, Polynomial.eval_finsetSum,
    bernsteinPolynomial, binomial_real_singleton, mul_comm]


theorem cdf_beta_int {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : 0≤t) :
    cdf (betaMeasure a b) t = ∫ x in (0:ℝ)..t, betaPDFReal a b x := by
  let := isProbabilityMeasureBeta ha hb
  rw [cdf_eq_real, MeasureTheory.measureReal_def, betaMeasure, withDensity_apply _ measurableSet_Iic]
  rw [← Set.Iic_union_Ioc_eq_Iic ht, lintegral_union measurableSet_Ioc (Set.Iic_disjoint_Ioc le_rfl)]
  rw [setLIntegral_eq_zero measurableSet_Iic (fun x hx => betaPDF_eq_zero_of_nonpos hx),zero_add]
  rw [intervalIntegral.integral_of_le ht, integral_eq_lintegral_of_nonneg_ae]
  · rfl
  · filter_upwards with x
    by_cases h : 0<x ∧ x<1
    · exact (betaPDFReal_pos h.1 h.2 ha hb).le
    · simp [betaPDFReal,h]
  · fun_prop

theorem tail_derivative_density (a b : ℕ) {t : ℝ} (ht : 0<t ∧ t<1) :
    ((tail (a+b+1) (a+1)).derivative).eval t =
      betaPDFReal (a+1) (b+1) t := by
  rw [derivative_tail (a+b) a (by omega)]
  simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_natCast,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
    Nat.add_sub_cancel_left, betaPDFReal, if_pos ht, add_sub_cancel_right,
    Real.rpow_natCast, beta, Real.Gamma_nat_eq_factorial]
  rw [show (a:ℝ)+1+(b+1) = ((a+b+1:ℕ):ℝ)+1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial, Nat.factorial_succ]
  have h : ((a+b).choose a:ℝ) * a.factorial * b.factorial = (a+b).factorial := by
    exact_mod_cast (by simpa using Nat.choose_mul_factorial_mul_factorial (show a ≤ a+b by omega) : (a+b).choose a * a.factorial * b.factorial = (a+b).factorial)
  push_cast
  field_simp
  linear_combination t^a*(1-t)^b*h

theorem cdf_succ (a b : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    cdf (betaMeasure (a+1) (b+1)) t = (tail (a+b+1) (a+1)).eval t := by
  rw [cdf_beta_int (by positivity) (by positivity) ht.1]
  let P := tail (a+b+1) (a+1)
  have hi : (∫ x in (0:ℝ)..t, P.derivative.eval x) = P.eval t - P.eval 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => P.hasDerivAt x)
      (P.derivative.continuous.intervalIntegrable ..)
  rw [intervalIntegral.integral_congr_Ioo_of_le ht.1 (g := fun x => P.derivative.eval x)
    (fun x hx => (tail_derivative_density a b ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩).symm), hi]
  simp [P, tail, eval_zero_weighted]

theorem cdf_tail (n k : ℕ) (hk : 0<k) (hn : k<n) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    cdf (betaMeasure k (↑(n-k) :ℝ)) t = (tail (n-1) k).eval t := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨b, he⟩ : ∃ b, n = a+b+2 := ⟨n-a-2, by omega⟩
  subst n
  simpa [show a+b+2-(a+1)=b+1 by omega, show a+b+2-1=a+b+1 by omega] using cdf_succ a b ht

theorem expectedExcess_integral (n k : ℕ) (hk : 0<k) (hn : k<n) (p : Set.Icc (0:ℝ) 1) :
    OMA.S_mo_403324.expectedExcess n k p =
      n * ∫ t in (0:ℝ)..(p:ℝ), cdf (betaMeasure k (↑(n-k):ℝ)) t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
  rw [expectedExcess_eq, ← intervalIntegral.integral_const_mul]
  let P := excess (m+1) k
  have hi : (∫ x in (0:ℝ)..(p:ℝ), P.derivative.eval x) = P.eval p.val - P.eval 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => P.hasDerivAt x)
      (P.derivative.continuous.intervalIntegrable ..)
  rw [intervalIntegral.integral_congr_Ioo_of_le p.2.1 (g := fun x => P.derivative.eval x)
    (fun x hx => by rw [cdf_tail _ _ hk hn ⟨hx.1.le, (hx.2.trans_le p.2.2).le⟩]
                    simp [P, derivative_excess]), hi]
  simp [P, excess, eval_zero_weighted]


theorem cdf_binomial_tail (n k : ℕ) (hk : 0<k) (hn : k<n) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    cdf (betaMeasure k (↑(n-k):ℝ)) t =
      ∑ x ∈ range n, if k≤x then ((n-1).choose x:ℝ)*t^x*(1-t)^(n-1-x) else 0 := by
  rw [cdf_tail n k hk hn ht]
  simp [tail, weighted, Polynomial.eval_finsetSum, bernsteinPolynomial,
    show n-1+1=n by omega, apply_ite, ite_mul]

end BetaNormalization

open Set Polynomial MeasureTheory Real
open scoped Polynomial
noncomputable section
namespace BetaNormalization

def logSlope (P : ℝ[X]) (t : ℝ) : ℝ := P.derivative.eval t / P.eval t

theorem primitive_pos (P : ℝ[X]) (hp : ∀ t ∈ Ioo (0:ℝ) 1, 0<P.derivative.eval t)
    (h0 : P.eval 0 = 0) : ∀ t ∈ Ioc (0:ℝ) 1, 0<P.eval t := by
  have hmono : StrictMonoOn (fun x => P.eval x) (Icc (0:ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ..) P.continuous.continuousOn
    intro x hx
    rw [(P.hasDerivAt x).deriv]
    exact hp x (by simpa using hx)
  intro t ht
  rw [← h0]
  exact hmono ⟨le_rfl,zero_le_one⟩ ⟨ht.1.le,ht.2⟩ ht.1

theorem logSlope_primitive (P : ℝ[X]) (hp : ∀ t ∈ Ioo (0:ℝ) 1, 0<P.derivative.eval t)
    (h0 : P.eval 0 = 0) (hd0 : 0≤P.derivative.eval 0)
    (hanti : AntitoneOn (logSlope P.derivative) (Ioo (0:ℝ) 1)) :
    AntitoneOn (logSlope P) (Ioo (0:ℝ) 1) := by
  have hpos := primitive_pos P hp h0
  have hd (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (logSlope P)
        ((P.derivative.derivative.eval x * P.eval x -
          P.derivative.eval x * P.derivative.eval x)/(P.eval x)^2) x :=
    (P.derivative.hasDerivAt x).div (P.hasDerivAt x) (hpos x ⟨hx.1,hx.2.le⟩).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Ioo ..)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
  · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  intro x hx
  have hx' := interior_subset hx
  rw [(hd x hx').deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hx'.1.le
    (f := fun s => P.derivative.derivative.eval x * P.derivative.eval s)
    (g := fun s => P.derivative.eval x * P.derivative.derivative.eval s)
    ((P.derivative.continuous.const_mul _).intervalIntegrable ..)
    ((P.derivative.derivative.continuous.const_mul _).intervalIntegrable ..)
    (fun s hs => by
      have hs' : s ∈ Ioo (0:ℝ) 1 := ⟨hs.1,hs.2.trans hx'.2⟩
      have h := (div_le_div_iff₀ (hp x hx') (hp s hs')).mp (hanti hs' hx' hs.2.le)
      linarith only [h])
  have intD (Q : ℝ[X]) : (∫ s in (0:ℝ)..x, Q.derivative.eval s) = Q.eval x - Q.eval 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => Q.hasDerivAt y)
      (Q.derivative.continuous.intervalIntegrable ..)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intD P,
    intD P.derivative, h0, sub_zero] at hi
  nlinarith [mul_nonneg (hp x hx').le hd0]

theorem logConcave_primitive (P : ℝ[X]) (hp : ∀ t ∈ Ioo (0:ℝ) 1, 0<P.derivative.eval t)
    (h0 : P.eval 0 = 0) (hanti : AntitoneOn (logSlope P) (Ioo (0:ℝ) 1)) :
    ConcaveOn ℝ (Ioc (0:ℝ) 1) (fun t => log (P.eval t)) := by
  have hpos := primitive_pos P hp h0
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioc ..)
  · exact P.continuous.continuousOn.log fun x hx => (hpos x hx).ne'
  · rw [interior_Ioc];intro x hx
    exact ((P.hasDerivAt x).log (hpos x ⟨hx.1,hx.2.le⟩).ne').differentiableAt.differentiableWithinAt
  · rw [interior_Ioc];intro x hx y hy hxy
    rw [((P.hasDerivAt x).log (hpos x ⟨hx.1,hx.2.le⟩).ne').deriv,
      ((P.hasDerivAt y).log (hpos y ⟨hy.1,hy.2.le⟩).ne').deriv]
    exact hanti hx hy hxy

theorem betaShapeSlope (Q : ℝ[X]) (a b : ℕ) {c : ℝ} (hc : 0<c)
    (hform : ∀ x, Q.eval x = c*x^a*(1-x)^b) :
    AntitoneOn (logSlope Q) (Ioo (0:ℝ) 1) := by
  have hder (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) :
      logSlope Q x = a/x - b/(1-x) := by
    have hx0 := hx.1
    have hx1 : 0<1-x := sub_pos.mpr hx.2
    have hQ : 0 < Q.eval x := by rw [hform]; positivity
    have hlog := ((Q.hasDerivAt x).log hQ.ne').deriv
    have h₁ := ((hasDerivAt_id x).log hx0.ne').const_mul (a:ℝ)
    have h₂ := ((((hasDerivAt_id x).const_sub 1).log hx1.ne').const_mul (b:ℝ))
    have h₃ := ((h₁.const_add (log c)).add h₂)
    have hcder := h₃.congr_of_eventuallyEq (f₁ := fun y => log (Q.eval y)) (by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      change log (Q.eval y) = log c + a*log y + b*log (1-y)
      rw [hform, log_mul (mul_ne_zero hc.ne' (pow_ne_zero _ hy.1.ne'))
        (pow_ne_zero _ (sub_pos.mpr hy.2).ne'), log_mul hc.ne' (pow_ne_zero _ hy.1.ne'),
        log_pow, log_pow])
    change Q.derivative.eval x / Q.eval x = _
    rw [← hlog, hcder.deriv]
    simp
    ring
  intro x hx y hy hxy
  rw [hder x hx,hder y hy]
  apply sub_le_sub
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg a) hx.1 hxy
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg b) (sub_pos.mpr hy.2) (by linarith)

theorem excess_shape (a b : ℕ) :
    ∀ t : ℝ, ((excess (a+b+2) (a+1)).derivative.derivative).eval t =
      (((a+b+2:ℕ):ℝ)*(a+b+1:ℕ)*(a+b).choose a)*t^a*(1-t)^b := by
  intro t
  rw [derivative_excess, Polynomial.derivative_mul, Polynomial.derivative_natCast,
    zero_mul, zero_add, derivative_tail (a+b) a (by omega)]
  simp [bernsteinPolynomial]
  ring

theorem excess_logConcave (a b : ℕ) :
    ConcaveOn ℝ (Ioc (0:ℝ) 1) (fun t => log ((excess (a+b+2) (a+1)).eval t)) := by
  let P := excess (a+b+2) (a+1)
  have hc : 0 < (((a+b+2:ℕ):ℝ)*(a+b+1:ℕ)*(a+b).choose a) := by
    positivity [Nat.choose_pos (show a≤a+b by omega)]
  have hshape := betaShapeSlope P.derivative.derivative a b hc (excess_shape a b)
  have hpp (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : 0<P.derivative.derivative.eval x := by
    dsimp only [P]
    rw [excess_shape]
    exact mul_pos (mul_pos hc (pow_pos hx.1 _)) (pow_pos (sub_pos.mpr hx.2) _)
  have hzero : P.eval 0 = 0 := by simp [P,excess,eval_zero_weighted]
  have hd0 : P.derivative.eval 0 = 0 := by
    simp [P,derivative_excess,tail,eval_zero_weighted]
  have hdd0 : 0≤P.derivative.derivative.eval 0 := by
    dsimp only [P]; rw [excess_shape]; positivity
  have hp (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : 0<P.derivative.eval x :=
    primitive_pos P.derivative hpp hd0 x ⟨hx.1,hx.2.le⟩
  exact logConcave_primitive P hp hzero (logSlope_primitive P hp hzero hd0.ge
    (logSlope_primitive P.derivative hpp hd0 hdd0 hshape))

end BetaNormalization

open Set Polynomial MeasureTheory ProbabilityTheory Real Finset OMA.S_mo_403324
open scoped Polynomial
noncomputable section
namespace BetaNormalization

theorem excess_positive {n k : ℕ} (hn : k<n) {t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) :
    0<(excess n k).eval t := by
  simp only [excess, weighted, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, bernsteinPolynomial, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  apply Finset.sum_pos' (fun i _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1.le _)) (pow_nonneg (sub_nonneg.mpr ht.2) _)))
  exact ⟨n, by simp, by simp [Nat.sub_pos_of_lt hn, ht.1]⟩

theorem excessLog (n k : ℕ) (hk : 0<k) (hn : k<n) :
    ConcaveOn ℝ (Ioc (0:ℝ) 1) (fun t => log ((excess n k).eval t)) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨b, he⟩ : ∃ b, n = a+b+2 := ⟨n-a-2, by omega⟩
  exact he ▸ excess_logConcave a b

def markedDensity (n k : ℕ) (p : Icc (0:ℝ) 1) (z : ℝ) : ℝ :=
  (n:ℝ)*p / expectedExcess n k p * cdf (betaMeasure k (↑(n-k):ℝ)) (p*(1-z))

theorem marked_survival (n k : ℕ) (p : Icc (0:ℝ) 1) (hk : 0<k) (hn : k<n)
    {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) :
    (∫ t in z..1, markedDensity n k p t) =
      (excess n k).eval ((p:ℝ)*(1-z)) / expectedExcess n k p := by
  let F := cdf (betaMeasure k (↑(n-k):ℝ))
  let q : Icc (0:ℝ) 1 := ⟨p*(1-z), mul_nonneg p.2.1 (sub_nonneg.mpr hz.2),
    (mul_le_mul_of_nonneg_right p.2.2 (sub_nonneg.mpr hz.2)).trans (by linarith [hz.1])⟩
  have hi := expectedExcess_integral n k hk hn q
  rw [expectedExcess_eq] at hi
  have changeVar := intervalIntegral.smul_integral_comp_sub_mul (a := z) (b := 1) F p.val p.val
  simp only [mul_one, sub_self, smul_eq_mul] at changeVar
  unfold markedDensity
  rw [intervalIntegral.integral_const_mul]
  change _ = (excess n k).eval (↑q) / _
  rw [hi]
  change _ = (n:ℝ) * (∫ t in (0:ℝ)..(p:ℝ)*(1-z), F t) / _
  simp_rw [mul_sub, mul_one]
  rw [← changeVar]
  ring

theorem marked_survival_concave (n k : ℕ) (p : Icc (0:ℝ) 1) (hk : 0<k) (hn : k<n)
    (hp : 0<(p:ℝ)) :
    ConcaveOn ℝ (Ico (0:ℝ) 1) (fun z => log (∫ t in z..1, markedDensity n k p t)) := by
  have qmem {z : ℝ} (hz : z ∈ Ico (0:ℝ) 1) : (p:ℝ)*(1-z) ∈ Ioc (0:ℝ) 1 :=
    ⟨mul_pos hp (sub_pos.mpr hz.2), (mul_le_mul_of_nonneg_right p.2.2 (sub_nonneg.mpr hz.2.le)).trans
      (by linarith [hz.1])⟩
  have ha : 0<expectedExcess n k p := by
    rw [expectedExcess_eq];exact excess_positive hn ⟨hp,p.2.2⟩
  have form {z : ℝ} (hz : z ∈ Ico (0:ℝ) 1) :
      log (∫ t in z..1, markedDensity n k p t) =
        log ((excess n k).eval ((p:ℝ)*(1-z))) - log (expectedExcess n k p) := by
    rw [marked_survival n k p hk hn ⟨hz.1,hz.2.le⟩, log_div (excess_positive hn (qmem hz)).ne' ha.ne']
  refine ⟨convex_Ico .., ?_⟩
  intro x hx y hy a b ha' hb' hab
  have hxy := (convex_Ico (𝕜:=ℝ) 0 1) hx hy ha' hb' hab
  dsimp only
  rw [form hx,form hy,form hxy]
  have h := (excessLog n k hk hn).2 (qmem hx) (qmem hy) ha' hb' hab
  simp only [smul_eq_mul] at h ⊢
  rw [show a*((p:ℝ)*(1-x))+b*(p*(1-y)) = p*(1-(a*x+b*y)) by
    linear_combination (p:ℝ) * hab] at h
  linear_combination h - log (expectedExcess n k p) * hab

end BetaNormalization
end
end
end
end

section
namespace MO403324Entropy
open MeasureTheory intervalIntegral Finset Real
noncomputable section

theorem beta_poly_integral (m i : ℕ) :
    (∫ z : ℝ in 0..1, z^m*(1-z)^i) =
      (m.factorial:ℝ)*i.factorial/(m+i+1).factorial := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have h := Complex.betaIntegral_eq_Gamma_mul_div ((m:ℂ)+1) ((i:ℂ)+1)
      (by simp; positivity) (by simp; positivity)
  rw [show ((m:ℂ)+1)+((i:ℂ)+1) = (↑(m+i+1):ℂ)+1 by push_cast; ring,
    Complex.Gamma_nat_eq_factorial,Complex.Gamma_nat_eq_factorial,Complex.Gamma_nat_eq_factorial] at h
  simpa [Complex.betaIntegral,Complex.cpow_natCast] using h

def rankPDF (m i : ℕ) (z : ℝ) : ℝ :=
  ((m+i+1:ℕ):ℝ)*(m+i).choose m * (z^m*(1-z)^i)

theorem rank_norm (m i : ℕ) : (∫ z in (0:ℝ)..1, rankPDF m i z) = 1 := by
  simp only [rankPDF,intervalIntegral.integral_const_mul,beta_poly_integral]
  rw [Nat.factorial_succ]
  push_cast
  have c : ((m+i).choose m:ℝ)*m.factorial*i.factorial=(m+i).factorial := by
    exact_mod_cast (by simpa using Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ m+i) : (m+i).choose m*m.factorial*i.factorial=(m+i).factorial)
  field_simp
  nlinarith

theorem rank_mean (m i : ℕ) : (∫ z in (0:ℝ)..1, z*rankPDF m i z) =
    ((m:ℝ)+1)/(m+i+2) := by
  have eq (z : ℝ) : z*rankPDF m i z =
      ((m+i+1:ℕ):ℝ)*(m+i).choose m * (z^(m+1)*(1-z)^i) := by
    simp only [rankPDF,pow_succ];ring
  simp only [eq,intervalIntegral.integral_const_mul,beta_poly_integral]
  rw [show m+1+i+1=(m+i+1)+1 by omega,Nat.factorial_succ (m+i+1),Nat.factorial_succ (m+i),Nat.factorial_succ m]
  push_cast
  have c : ((m+i).choose m:ℝ)*m.factorial*i.factorial=(m+i).factorial := by
    exact_mod_cast (by simpa using Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ m+i) : (m+i).choose m*m.factorial*i.factorial=(m+i).factorial)
  field_simp
  nlinarith

theorem rank_log_integrable (m i : ℕ) :
    IntervalIntegrable (fun z : ℝ => -Real.log z*rankPDF m i z) volume 0 1 :=
  intervalIntegrable_log'.neg.mul_continuousOn (by unfold rankPDF; fun_prop)

theorem rank_entropy (m i : ℕ) :
    Real.log (((m:ℝ)+i+2)/(m+1)) ≤ ∫ z in (0:ℝ)..1, -Real.log z * rankPDF m i z := by
  let q : ℝ := ((m:ℝ)+1)/(m+i+2)
  have hq : 0 < q := by dsimp [q];positivity
  have hlog : Real.log (((m:ℝ)+i+2)/(m+1)) = -Real.log q := by
    dsimp [q]; rw [←Real.log_inv,inv_div]
  rw [hlog]
  have term (z : ℝ) (hz : z ∈ Set.Ioo (0:ℝ) 1) :
      (1-Real.log q)*rankPDF m i z-(1/q)*(z*rankPDF m i z) ≤
      -Real.log z*rankPDF m i z := by
    have h := Real.log_le_sub_one_of_pos (div_pos hz.1 hq)
    rw [Real.log_div hz.1.ne' hq.ne'] at h
    have hw : 0 ≤ rankPDF m i z := by unfold rankPDF;positivity [hz.1,sub_pos.mpr hz.2]
    have hc : 1-Real.log q-z/q ≤ -Real.log z := by linarith
    calc
      _ = (1-Real.log q-z/q)*rankPDF m i z := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hw
  have h1 : IntervalIntegrable (fun z : ℝ => (1-Real.log q)*rankPDF m i z) volume 0 1 :=
    (show Continuous _ by unfold rankPDF; fun_prop).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun z : ℝ => (1/q)*(z*rankPDF m i z)) volume 0 1 :=
    (show Continuous _ by unfold rankPDF; fun_prop).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ)≤1)
    (h1.sub h2) (rank_log_integrable m i) term
  rw [intervalIntegral.integral_sub h1 h2,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,rank_norm,rank_mean] at h
  change (1-Real.log q)*1-1/q*q ≤ _ at h
  simpa [hq.ne'] using h

theorem log_choose_le (x j : ℕ) (hj : j ≤ x) :
    Real.log (x.choose j) ≤ ∑ r ∈ range j, Real.log (((x:ℝ)+1)/(r+1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hC : 0 < (x.choose j:ℝ) := by exact_mod_cast Nat.choose_pos (by omega : j ≤ x)
    have hD : 0 < (x.choose (j+1):ℝ) := by exact_mod_cast Nat.choose_pos hj
    have q : (x.choose (j+1):ℝ)*((j:ℝ)+1) = (x.choose j:ℝ)*((x-j:ℕ):ℝ) := by
      exact_mod_cast Nat.choose_succ_right_eq x j
    have le : (x.choose (j+1):ℝ) ≤ (x.choose j:ℝ)*(((x:ℝ)+1)/(j+1)) := by
      rw [←mul_div_assoc,le_div_iff₀ (by positivity)]
      rw [q];gcongr;exact_mod_cast (by omega : x-j ≤ x+1)
    rw [sum_range_succ]
    exact (Real.log_le_log hD le).trans (by rw [Real.log_mul hC.ne' (by positivity : (((x:ℝ)+1)/(j+1)) ≠ 0)];gcongr;exact ih (by omega))
/-- The conditional ranked contribution when exactly x sample points fall below p. -/
def rankSum (k x : ℕ) (z : ℝ) : ℝ :=
  ∑ m ∈ range (x-k), rankPDF m (x-1-m) z

theorem rankSum_log_integrable (k x : ℕ) :
    IntervalIntegrable (fun z : ℝ => -Real.log z*rankSum k x z) volume 0 1 := by
  exact intervalIntegrable_log'.neg.mul_continuousOn (by unfold rankSum rankPDF; fun_prop)

theorem log_choose_le_rankSum (k x : ℕ) :
    Real.log (x.choose (x-k)) ≤ ∫ z in (0:ℝ)..1, -Real.log z*rankSum k x z := by
  simp only [rankSum,Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun m _ => rank_log_integrable m (x-1-m))]
  apply (log_choose_le x (x-k) (by omega)).trans
  apply Finset.sum_le_sum
  intro m hm
  have hmx := mem_range.mp hm
  have hi : m+(x-1-m)+1=x := by omega
  have H := rank_entropy m (x-1-m)
  have E : (m:ℝ)+(↑(x-1-m):ℝ)+2=x+1 := by exact_mod_cast (by omega : m+(x-1-m)+2=x+1)
  rwa [E] at H

theorem weighted_entropy (N k : ℕ) (w : ℕ → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x ∈ range (N+1), w x*Real.log (x.choose (x-k))) ≤
      ∫ z in (0:ℝ)..1, -Real.log z*(∑ x ∈ range (N+1), w x*rankSum k x z) := by
  simp only [Finset.mul_sum]
  have eq (z : ℝ) (x : ℕ) : -Real.log z*(w x*rankSum k x z) = w x*(-Real.log z*rankSum k x z) := by ring
  simp_rw [eq]
  rw [intervalIntegral.integral_finsetSum (fun x _ => (rankSum_log_integrable k x).const_mul (w x))]
  simp only [intervalIntegral.integral_const_mul]
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (log_choose_le_rankSum k x) (hw x)

def weight (n : ℕ) (p : ℝ) (x : ℕ) : ℝ := (n.choose x)*p^x*(1-p)^(n-x)
def tail (n k : ℕ) (t : ℝ) : ℝ := ∑ i ∈ range (n+1), if k ≤ i then weight n t i else 0

private lemma choose_split (N i m : ℕ) :
    (N+1)*N.choose i*(N-i).choose m =
    (N+1).choose (i+m+1)*(i+m+1)*(i+m).choose m := by
  rw [←Nat.add_one_mul_choose_eq N (i+m),mul_assoc,mul_assoc,←Nat.choose_symm_add (a:=i) (b:=m),Nat.choose_mul (s:=i) (by omega : i ≤ i+m),Nat.add_sub_cancel_left]

/-- Grouping the same trinomial masses first by the number below the mark, then by the total count. -/
theorem mixture (N k : ℕ) (p z : ℝ) :
    ((N:ℝ)+1)*p *tail N k (p*(1-z)) =
      ∑ x ∈ range (N+2), weight (N+1) p x*rankSum k x z := by
  let f (i m : ℕ) := if k ≤ i then weight (N+1) p (i+m+1)*rankPDF m i z else 0
  have split (i : ℕ) (hi : i ≤ N) :
      ((N:ℝ)+1)*p*(if k ≤ i then weight N (p*(1-z)) i else 0) =
      ∑ m ∈ range (N+1-i), f i m := by
    by_cases eligible : k ≤ i
    · simp only [f,if_pos eligible,weight,rankPDF]
      rw [show 1-p*(1-z)=p*z+(1-p) by ring,add_pow,show N+1-i=N-i+1 by omega]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have h1 : N+1-(i+m+1)=N-i-m := by omega
      rw [h1,show m+i=i+m by omega,pow_succ,pow_add,mul_pow,mul_pow]
      have cs : ((N:ℝ)+1)*(N.choose i:ℝ)*((N-i).choose m:ℝ) =
          ((N+1).choose (i+m+1):ℝ)*(i+m+1)*((i+m).choose m:ℝ) := by
        exact_mod_cast choose_split N i m
      push_cast
      linear_combination (norm := ring_nf) p*p^i*p^m*(1-z)^i*z^m*(1-p)^(N-i-m)*cs
    · simp [f,eligible]
  unfold tail
  rw [Finset.mul_sum]
  calc
    _ = ∑ i ∈ range (N+1), ∑ m ∈ range (N+1-i), f i m :=
      Finset.sum_congr rfl (fun i hi => split i (by have := mem_range.mp hi;omega))
    _ = ∑ s ∈ range (N+1), ∑ i ∈ range (s+1), f i (s-i) := (Finset.sum_range_diag_flip (N+1) f).symm
    _ = _ := by
      rw [Finset.sum_range_succ' (fun x => weight (N+1) p x*rankSum k x z)]
      simp only [rankSum, Nat.zero_sub,range_zero,sum_empty,mul_zero,add_zero]
      apply Finset.sum_congr rfl
      intro s hs
      rw [←Finset.sum_range_reflect (fun i => f i (s-i)) (s+1),Finset.mul_sum]
      have incl : range (s+1-k) ⊆ range (s+1) := range_mono (Nat.sub_le ..)
      calc
        _ = ∑ m ∈ range (s+1), if m < s+1-k then weight (N+1) p (s+1)*rankPDF m (s-m) z else 0 := by
          apply Finset.sum_congr rfl
          intro m hm
          have h := mem_range.mp hm
          simp only [Nat.add_sub_cancel,f]
          rw [show s-(s-m)=m by omega,show s-m+m+1=s+1 by omega]
          by_cases E : k ≤ s-m
          · simp [E,show m < s+1-k by omega]
          · simp [E,show ¬m < s+1-k by omega]
        _ = _ := by
          rw [←Finset.sum_subset incl (f:=fun m => if m < s+1-k then weight (N+1) p (s+1)*rankPDF m (s-m) z else 0) (fun m _ h => by simp [show ¬m < s+1-k by simpa using h])]
          apply Finset.sum_congr rfl
          intro m hm; simp [mem_range.mp hm]

/-- The unnormalized excess density integrates to the expected excess. -/
theorem mixture_mass (N k : ℕ) (p : ℝ) :
    (∫ z in (0:ℝ)..1, ((N:ℝ)+1)*p*tail N k (p*(1-z))) =
    ∑ x ∈ range (N+2), weight (N+1) p x*((x-k:ℕ):ℝ) := by
  simp_rw [mixture]
  have c (x : ℕ) : Continuous (fun z => weight (N+1) p x * rankSum k x z) := by
    unfold rankSum rankPDF;fun_prop
  rw [intervalIntegral.integral_finsetSum (fun x _ => (c x).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro x _
  simp only [intervalIntegral.integral_const_mul,rankSum]
  rw [intervalIntegral.integral_finsetSum (fun m _ => (show Continuous (rankPDF m (x-1-m)) by unfold rankPDF;fun_prop).intervalIntegrable _ _)]
  simp [rank_norm]

open ProbabilityTheory

/-- This includes p=1. The only premise about F is the standard binomial-tail formula for its CDF. -/
theorem finite_entropy_bridge (n k : ℕ) (p : Set.Icc (0:ℝ) 1) (hkn : k < n)
    (hp : 0 < (p:ℝ)) (F : ℝ → ℝ)
    (hF : ∀ t ∈ Set.Icc (0:ℝ) 1, F t=tail (n-1) k t) :
    let a := ∑ x ∈ range (n+1), (binomial n p).real {x} * ((x-k:ℕ):ℝ)
    let b := ∑ x ∈ range (n+1), (binomial n p).real {x} * Real.log (x.choose (x-k))
    0 < a ∧ b/a ≤ ∫ z in (0:ℝ)..1, -Real.log z*((n:ℝ)*p*F (p*(1-z))/a) := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [binomial_real_singleton]
  let a := ∑ x ∈ range (N+2), weight (N+1) p x*((x-k:ℕ):ℝ)
  have wpos (x : ℕ) : 0 ≤ weight (N+1) p x := by
    unfold weight; positivity [p.property.1,sub_nonneg.mpr p.property.2]
  have a0 : 0 < a := by
    have H := Finset.single_le_sum (f:=fun x => weight (N+1) p x*((x-k:ℕ):ℝ))
      (fun x _ => mul_nonneg (wpos x) (Nat.cast_nonneg _)) (show N+1 ∈ range (N+2) by simp)
    have wp : 0 < weight (N+1) p (N+1) := by simp [weight]; positivity
    exact (mul_pos wp (by exact_mod_cast (by omega : 0 < N+1-k))).trans_le H
  refine ⟨a0,?_⟩
  change _ / a ≤ (∫ z in (0:ℝ)..1, -Real.log z*(((N+1:ℕ):ℝ)*p*F (p*(1-z))/a))
  have ht (z : ℝ) (hz : z ∈ Set.uIcc (0:ℝ) 1) :
      p.val*(1-z) ∈ Set.Icc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num)] at hz
    exact ⟨mul_nonneg hp.le (sub_nonneg.mpr hz.2), by
      calc
        p.val*(1-z) ≤ p.val*1 := mul_le_mul_of_nonneg_left (by linarith [hz.1]) hp.le
        _ ≤ 1 := by simpa using p.property.2⟩
  calc
    _ ≤ (∫ z in (0:ℝ)..1, -Real.log z*(∑ x ∈ range (N+2), weight (N+1) p x*rankSum k x z))/a :=
      div_le_div_of_nonneg_right (weighted_entropy (N+1) k (weight (N+1) p) wpos) a0.le
    _ = _ := by
      rw [←intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro z hz
      dsimp only
      rw [hF _ (ht _ hz),show N.succ-1=N by omega,←mixture]
      push_cast
      ring
end
end MO403324Entropy
end

section
open ProbabilityTheory MeasureTheory OMA.S_mo_403324
namespace MO403324Entropy

theorem source_bridge (n k : ℕ) (p : Set.Icc (0 : ℝ) 1) (hk : 0 < k)
    (hn : k < n) (hp : 0 < (p : ℝ)) :
    0 < expectedExcess n k p ∧
      expectedLogChoose n k p / expectedExcess n k p ≤
        ∫ z in (0 : ℝ)..1, -Real.log z *
          ((n:ℝ)*p*cdf (betaMeasure k (↑(n-k):ℝ)) (p*(1-z)) / expectedExcess n k p) := by
  apply finite_entropy_bridge n k p hn hp
  intro t ht
  simpa only [tail,weight,show n-1+1=n by omega] using BetaNormalization.cdf_binomial_tail n k hk hn ht

end MO403324Entropy
end

section
open MeasureTheory Real
namespace BetaFinal

theorem weighted (f : ℝ → ℝ) {m : ℝ} (hm : 0 < m)
    (hf : ∀ z ∈ Set.Icc (0:ℝ) 1, 0 ≤ f z)
    (hi : IntervalIntegrable (fun z => exp (z / (2*m)) * f z) volume 0 1)
    (hg : (∫ z in (0:ℝ)..1, exp (z / (2*m)) * f z) ≤ 2) :
    (∫ z in (0:ℝ)..1, sqrt (f z)) ≤ 2 * sqrt m := by
  by_cases hs : IntervalIntegrable (fun z => sqrt (f z)) volume 0 1
  · have hr := Real.sqrt_pos.2 hm
    have hn : IntervalIntegrable (fun z : ℝ => exp (z / (-(2*m)))) volume 0 1 :=
      (by fun_prop : Continuous (fun z : ℝ => exp (z / (-(2*m))))).intervalIntegrable _ _
    have hb : (∫ z in (0:ℝ)..1, exp (z / (-(2*m)))) ≤ 2*m := by
      rw [intervalIntegral.integral_comp_div Real.exp (by linarith : -(2*m) ≠ 0), integral_exp]
      simp only [zero_div, exp_zero, smul_eq_mul]
      nlinarith [mul_pos hm (exp_pos (1 / -(2*m)))]
    have hw := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      (hs.const_mul 2) ((hi.const_mul (sqrt m)).add (hn.const_mul (1 / sqrt m))) (by
        intro z hz
        rw [div_neg, exp_neg]
        have hE := exp_pos (z / (2*m))
        field_simp
        nlinarith [sq_nonneg (sqrt m * exp (z/(2*m)) * sqrt (f z) - 1),
          Real.sq_sqrt (hf z hz),
          show (sqrt m * exp (z/(2*m)) * sqrt (f z))^2 =
            (sqrt m)^2 * exp (z/(2*m))^2 * f z by
              rw [mul_pow, mul_pow, Real.sq_sqrt (hf z hz)]])
    rw [intervalIntegral.integral_add (hi.const_mul _) (hn.const_mul _)] at hw
    simp only [intervalIntegral.integral_const_mul] at hw
    have h := add_le_add (mul_le_mul_of_nonneg_left hg hr.le)
      (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1 / sqrt m))
    have he : 1 / sqrt m * (2*m) = 2 * sqrt m := by
      field_simp
      nlinarith [Real.sq_sqrt hm.le]
    linarith
  · rw [intervalIntegral.integral_undef hs]
    positivity

theorem finalScalar {m q I : ℝ} (hm : 0 < m) (hI : I ≤ 2 * sqrt m)
    (hq : q ≤ eulerMascheroniConstant - log m) : I ≤ 3 * exp (-q/2) := by
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < (3/2)⁻¹)
  rw [Real.log_inv] at hl
  norm_num at hl
  have he : exp ((q + log m)/2) ≤ 3/2 := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 3/2)]
    apply Real.exp_le_exp.mpr
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hs : exp (log m / 2) = sqrt m := by
    have hh : exp (log m / 2) ^ 2 = m := by
      rw [sq, ← Real.exp_add, show log m / 2 + log m / 2 = log m by ring, Real.exp_log hm]
    nlinarith [sqrt_nonneg m, exp_pos (log m / 2), Real.sq_sqrt hm.le]
  have hh := mul_le_mul_of_nonneg_right he (exp_pos (-q/2)).le
  rw [← Real.exp_add, show (q + log m)/2 + -q/2 = log m/2 by ring, hs] at hh
  linarith

theorem changeVariables (F : ℝ → ℝ) {N p a : ℝ} (hN : 0 ≤ N) (hp : 0 < p) (ha : 0 < a) :
    sqrt N * (∫ t in (0:ℝ)..p, sqrt (F t)) =
      sqrt (a*p) * (∫ z in (0:ℝ)..1, sqrt ((N*p/a)*F (p*(1-z)))) := by
  have hh := intervalIntegral.smul_integral_comp_sub_mul (a := 0) (b := 1)
    (fun t => sqrt (F t)) p p
  simp only [mul_one, sub_self, mul_zero, sub_zero, smul_eq_mul] at hh
  simp_rw [Real.sqrt_mul (by positivity : 0 ≤ N*p/a), mul_sub, mul_one]
  rw [intervalIntegral.integral_const_mul, ← mul_assoc, ← Real.sqrt_mul (by positivity)]
  rw [show a*p*(N*p/a) = p^2*N by field_simp, Real.sqrt_mul (sq_nonneg p),
    Real.sqrt_sq hp.le, ← hh]
  ring

theorem finalBound (F : ℝ → ℝ) {N p a b m : ℝ} (hN : 0 ≤ N) (hp : 0 < p) (ha : 0 < a)
    (hm : 0 < m) (hq : b/a ≤ eulerMascheroniConstant - log m)
    (hf : ∀ z ∈ Set.Icc (0:ℝ) 1, 0 ≤ (N*p/a)*F (p*(1-z)))
    (hi : IntervalIntegrable (fun z => exp (z/(2*m))*((N*p/a)*F (p*(1-z)))) volume 0 1)
    (hg : (∫ z in (0:ℝ)..1, exp (z/(2*m))*((N*p/a)*F (p*(1-z)))) ≤ 2) :
    sqrt N * (∫ t in (0:ℝ)..p, sqrt (F t)) ≤ 3 * sqrt (a*p) * exp (b/(-2*a)) := by
  rw [changeVariables F hN hp ha]
  have hb := finalScalar hm (weighted _ hm hf hi hg) hq
  have he : -(b/a)/2 = b/(-2*a) := by ring
  rw [he] at hb
  calc
    _ ≤ sqrt (a*p) * (3 * exp (b/(-2*a))) := mul_le_mul_of_nonneg_left hb (sqrt_nonneg _)
    _ = _ := by ring


end BetaFinal
end

section
open ProbabilityTheory MeasureTheory Real Finset OMA.S_mo_403324

theorem excess_pos {n k : ℕ} (p : Set.Icc (0:ℝ) 1) (hkn : k<n) (hp : 0<(p:ℝ)) :
    0 < expectedExcess n k p := by
  unfold expectedExcess
  apply Finset.sum_pos'
  · intro i hi
    positivity
  · refine ⟨n, by simp, ?_⟩
    rw [binomial_real_singleton]
    simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, one_mul]
    exact mul_pos (by positivity) (by exact_mod_cast Nat.sub_pos_of_lt hkn)

theorem cdf_integrable_weight (D : Measure ℝ) {p m c : ℝ} (hp : 0≤p) :
    IntervalIntegrable (fun z => exp (z/(2*m))*(c*cdf D (p*(1-z)))) volume 0 1 := by
  have h : Antitone (fun z : ℝ => cdf D (p*(1-z))) := by
    intro x y hxy
    exact monotone_cdf D (mul_le_mul_of_nonneg_left (by linarith) hp)
  exact ((h.intervalIntegrable (μ := volume) (a := 0) (b := 1)).const_mul c).continuousOn_mul
    (by fun_prop)
end

section
open MeasureTheory ProbabilityTheory Real OMA.S_mo_403324
namespace MO403324Glue
noncomputable section

def density (n k : ℕ) (p : Set.Icc (0:ℝ) 1) (z : ℝ) : ℝ :=
  ((n:ℝ)*p/expectedExcess n k p)*cdf (betaMeasure k (↑(n-k):ℝ)) (p*(1-z))

def mean (n k : ℕ) (p : Set.Icc (0:ℝ) 1) : ℝ :=
  ∫ z in (0:ℝ)..1, z*density n k p z

theorem density_norm (n k : ℕ) (p : Set.Icc (0:ℝ) 1) (hk : 0 < k) (hn : k < n)
    (hp : 0 < (p:ℝ)) : (∫ z in (0:ℝ)..1, density n k p z)=1 := by
  let F := cdf (betaMeasure k (↑(n-k):ℝ))
  have he := BetaNormalization.expectedExcess_integral n k hk hn p
  change expectedExcess n k p=(n:ℝ)*(∫ t in (0:ℝ)..(p:ℝ), F t) at he
  have q := intervalIntegral.smul_integral_comp_sub_mul (a:=0) (b:=1) (fun t => F t) p.val p.val
  simp only [mul_one,sub_self,mul_zero,sub_zero,smul_eq_mul] at q
  change (∫ z in (0:ℝ)..1, ((n:ℝ)*p/expectedExcess n k p)*F (p*(1-z)))=1
  rw [intervalIntegral.integral_const_mul]
  have eq (z : ℝ) : p.val-p.val*z=p.val*(1-z) := by ring
  simp_rw [eq] at q
  have ha := excess_pos p hn hp
  field_simp
  linear_combination (n:ℝ)*q - he

theorem density_continuousOn (n k : ℕ) (p : Set.Icc (0:ℝ) 1)
    (hk : 0 < k) (hn : k < n) :
    ContinuousOn (density n k p) (Set.Icc 0 1) := by
  let P := BetaNormalization.tail (n-1) k
  apply (show ContinuousOn (fun z : ℝ => ((n:ℝ)*p/expectedExcess n k p)*P.eval (p*(1-z))) (Set.Icc 0 1) by fun_prop).congr
  intro z hz
  have ht : p.val*(1-z) ∈ Set.Icc (0:ℝ) 1 := ⟨mul_nonneg p.property.1 (sub_nonneg.mpr hz.2),
    (mul_le_mul_of_nonneg_left (show 1-z≤1 by linarith [hz.1]) p.property.1).trans (by simpa using p.property.2)⟩
  simp only [density,BetaNormalization.cdf_tail n k hk hn ht,P]

theorem density_pos (n k : ℕ) (p : Set.Icc (0:ℝ) 1) (hk : 0 < k) (hn : k < n)
    (hp : 0 < (p:ℝ)) (z : ℝ) (hz : z ∈ Set.Ioo (0:ℝ) 1) : 0 < density n k p z := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have ht0 : 0 < p.val*(1-z) := mul_pos hp (sub_pos.mpr hz.2)
  have ht1 : p.val*(1-z) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (show 1-z≤1 by linarith [hz.1]) hp.le).trans (by simpa using p.property.2)
  unfold density
  apply mul_pos (div_pos (mul_pos hn0 hp) (excess_pos p hn hp))
  rw [BetaNormalization.cdf_binomial_tail n k hk hn ⟨ht0.le,ht1⟩]
  apply Finset.sum_pos'
  · intro i hi;split_ifs <;> positivity [ht0,sub_nonneg.mpr ht1]
  · refine ⟨n-1,Finset.mem_range.mpr (by omega),?_⟩
    simp [show k≤n-1 by omega]; positivity

theorem mean_pos (n k : ℕ) (p : Set.Icc (0:ℝ) 1) (hk : 0 < k) (hn : k < n)
    (hp : 0 < (p:ℝ)) : 0 < mean n k p := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ (by norm_num)
  · exact ((continuousOn_id.mul (density_continuousOn n k p hk hn))).intervalIntegrable_of_Icc (by norm_num)
  · intro z hz;exact mul_pos hz.1 (density_pos n k p hk hn hp z hz)

/-- The two moment comparisons suffice for the original question, without any further side conditions. -/
theorem source_conditional (n k : ℕ) (p : Set.Icc (0:ℝ) 1) (hk : 0 < k) (hn : k < n)
    (hp : 0 < (p:ℝ))
    (hlog : (∫ z in (0:ℝ)..1, -Real.log z*density n k p z) ≤
        eulerMascheroniConstant -Real.log (mean n k p))
    (htilt : (∫ z in (0:ℝ)..1, Real.exp (z/(2*mean n k p))*density n k p z) ≤ 2) :
    sqrt (n:ℝ)*(∫ t in (0:ℝ)..(p:ℝ), sqrt (cdf (betaMeasure k (↑(n-k):ℝ)) t)) ≤
      3*sqrt (expectedExcess n k p*p)*exp (expectedLogChoose n k p/(-2*expectedExcess n k p)) := by
  have H := MO403324Entropy.source_bridge n k p hk hn hp
  apply BetaFinal.finalBound _ (Nat.cast_nonneg n) hp H.1 (mean_pos n k p hk hn hp) _ _ _ htilt
  · refine H.2.trans (le_trans ?_ hlog)
    apply le_of_eq
    apply intervalIntegral.integral_congr
    intro z _;dsimp [density];ring
  · intro z _;exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hp.le) H.1.le) (cdf_nonneg _ _)
  · exact cdf_integrable_weight _ hp.le

end
end MO403324Glue
end

section
open Set Filter MeasureTheory Real
open scoped Topology
namespace BetaExponential

theorem unitLog :
    (∫ x : ℝ in Ioi 0, log x * exp (-x)) = -eulerMascheroniConstant := by
  have hh := Complex.hasDerivAt_GammaIntegral (s := 1) (by norm_num)
  have hn : Complex.Gamma =ᶠ[𝓝 1] Complex.GammaIntegral := by
    have ho : IsOpen {s : ℂ | 0 < s.re} :=
      Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
    filter_upwards [ho.mem_nhds (by norm_num : (1:ℂ) ∈ {s : ℂ | 0 < s.re})] with s hs
    exact Complex.Gamma_eq_integral hs
  have he := (hh.congr_of_eventuallyEq hn).unique Complex.hasDerivAt_Gamma_one
  simp only [sub_self, Complex.cpow_zero, one_mul, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg] at he
  rw [integral_complex_ofReal] at he
  exact_mod_cast he

theorem logMoment {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (-log x)*(a⁻¹*exp (-x/a))) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0, (-log x)*(a⁻¹*exp (-x/a))) = eulerMascheroniConstant - log a := by
  have hc := integral_comp_mul_left_Ioi (fun x : ℝ => log x * exp (-x)) 0 (inv_pos.mpr ha)
  simp only [mul_zero, inv_inv, smul_eq_mul, unitLog] at hc
  have hi : IntegrableOn (fun x : ℝ => log (a⁻¹*x) * exp (-(a⁻¹*x))) (Ioi 0) := by
    by_contra h
    rw [integral_undef h] at hc
    have hg := Real.one_half_lt_eulerMascheroniConstant
    nlinarith [mul_pos ha (show 0 < eulerMascheroniConstant by linarith)]
  have he := integrableOn_exp_mul_Ioi (a := -a⁻¹) (by exact neg_lt_zero.mpr (by positivity)) 0
  have hv := integral_exp_mul_Ioi (a := -a⁻¹) (by exact neg_lt_zero.mpr (by positivity)) 0
  simp at hv
  have eqn : (fun x : ℝ => (-log x)*(a⁻¹*exp (-x/a))) =ᵐ[volume.restrict (Ioi 0)]
      fun x => (-a⁻¹)*(log (a⁻¹*x)*exp (-(a⁻¹*x))) +
        (-log a * a⁻¹)*exp (-a⁻¹*x) := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0:ℝ)) measurableSet_Ioi] with x hx
    rw [Real.log_mul (inv_ne_zero ha.ne') (ne_of_gt hx), Real.log_inv]
    simp only [neg_mul, div_eq_inv_mul]
    ring
  constructor
  · exact ((hi.const_mul _).add (he.const_mul _)).congr eqn.symm
  · rw [integral_congr_ae eqn, integral_add (hi.const_mul _) (he.const_mul _),
      integral_const_mul, integral_const_mul, hc]
    simp_rw [neg_mul]
    rw [hv]
    field_simp
    ring

theorem expMoment {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => exp (x/(2*a))*(a⁻¹*exp (-x/a))) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0, exp (x/(2*a))*(a⁻¹*exp (-x/a))) = 2 := by
  have hneg : -(2*a)⁻¹ < 0 := by exact neg_lt_zero.mpr (by positivity)
  have e (x : ℝ) : exp (x/(2*a))*(a⁻¹*exp (-x/a)) = a⁻¹*exp (-(2*a)⁻¹*x) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  simp_rw [e]
  refine ⟨(integrableOn_exp_mul_Ioi hneg 0).const_mul _, ?_⟩
  rw [integral_const_mul, integral_exp_mul_Ioi hneg]
  simp
  field_simp

end BetaExponential
end

section
open Filter Set MeasureTheory Real
open scoped Topology

namespace BetaIFR

/-- The strict split permits a jump or a flat region of equality at the cutoff. -/
theorem survival_crossing {S : ℝ → ℝ} {L m : ℝ} (hL : 0 < L)
    (hzero : S 0 = 1) (hpos : ∀ x ∈ Ico 0 L, 0 < S x)
    (hend : ∀ x, L ≤ x → S x = 0)
    (hlog : ConcaveOn ℝ (Ico 0 L) (fun x ↦ log (S x))) :
    ∃ c ∈ Icc 0 L, (∀ x ∈ Ioo 0 c, exp (-x / m) ≤ S x) ∧
      (∀ x, c < x → S x < exp (-x / m)) := by
  let A := {x : ℝ | 0 ≤ x ∧ exp (-x / m) ≤ S x}
  have h0 : 0 ∈ A := by simp [A, hzero]
  have hbound : ∀ x ∈ A, x < L := by
    intro x hx
    by_contra! h
    exact (not_lt_of_ge hx.2) (by rw [hend x h]; exact exp_pos _)
  have hb : BddAbove A := ⟨L, fun x hx ↦ (hbound x hx).le⟩
  refine ⟨sSup A, ⟨le_csSup hb h0, csSup_le ⟨0,h0⟩ fun x hx ↦ (hbound x hx).le⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup ⟨0,h0⟩ hx.2
    have hyL := hbound y hy
    have hxL : x < L := hxy.trans hyL
    have hy0 := hx.1.trans hxy
    have hsl := hlog.antitoneOn_slope_gt (x := 0) ⟨le_rfl,hL⟩
      (show x ∈ {z ∈ Ico 0 L | 0 < z} from ⟨⟨hx.1.le,hxL⟩,hx.1⟩)
      (show y ∈ {z ∈ Ico 0 L | 0 < z} from ⟨⟨hy0.le,hyL⟩,hy0⟩) hxy.le
    simp [slope_def_field, hzero] at hsl
    have hyl := log_le_log (exp_pos _) hy.2
    rw [log_exp] at hyl
    apply (le_log_iff_exp_le (hpos x ⟨hx.1.le,hxL⟩)).mp
    have hl : -(1 / m) ≤ log (S y) / y := (le_div_iff₀ hy0).mpr <|
      calc -(1 / m) * y = -y / m := by ring
           _ ≤ _ := hyl
    calc -x / m = -(1 / m) * x := by ring
         _ ≤ _ := (le_div_iff₀ hx.1).mp (hl.trans hsl)
  · intro x hx
    by_contra! h
    exact (not_lt_of_ge (le_csSup hb (show x ∈ A from
      ⟨(le_csSup hb h0).trans hx.le,h⟩))) hx

theorem exp_tail_integral {m : ℝ} (hm : 0 < m) (a : ℝ) :
    (∫ x in Ioi a, exp (-x / m)) = m * exp (-a / m) := by
  simp_rw [show ∀ x : ℝ, -x / m = (-m⁻¹) * x by intro x; ring]
  rw [integral_exp_mul_Ioi (neg_lt_zero.mpr (inv_pos.mpr hm))]
  field_simp

theorem exp_tail_integrable {m : ℝ} (hm : 0 < m) (a : ℝ) :
    IntegrableOn (fun x ↦ exp (-x / m)) (Ioi a) := by
  simp_rw [show ∀ x : ℝ, -x / m = -m⁻¹ * x by intro x; ring]
  exact
    exp_neg_integrableOn_Ioi a (inv_pos.mpr hm)

/-- Equal means and the strictly positive exponential tail beyond L force c > 0. -/
theorem crossing_pos {S : ℝ → ℝ} {m L c : ℝ} (hm : 0 < m) (hL : 0 < L)
    (hc : 0 ≤ c) (hr : ∀ x, c < x → S x ≤ exp (-x / m))
    (hend : ∀ x, L ≤ x → S x = 0) (hS : IntegrableOn S (Ioi 0))
    (hmean : (∫ x in Ioi 0, S x) = m) : 0 < c := by
  by_contra! h
  have hc0 : c = 0 := le_antisymm h hc
  have hSL : (∫ x in Ioi L, S x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact fun x hx ↦ hend x hx.le
  have part (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) :
      (∫ x in Ioc 0 L, f x) + (∫ x in Ioi L, f x) = ∫ x in Ioi 0, f x := by
    rw [← setIntegral_union (by exact Set.disjoint_left.mpr fun x hx h ↦ (not_lt_of_ge hx.2) h)
      measurableSet_Ioi (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hL.le)),
      Ioc_union_Ioi_eq_Ioi hL.le]
  have hmono : (∫ x in Ioc 0 L, S x) ≤ ∫ x in Ioc 0 L, exp (-x / m) := by
    apply setIntegral_mono_on (hS.mono_set Ioc_subset_Ioi_self)
      ((exp_tail_integrable hm 0).mono_set Ioc_subset_Ioi_self) measurableSet_Ioc
    exact fun x hx ↦ hr x (hc0 ▸ hx.1)
  have h1 := part S hS
  have h2 := part _ (exp_tail_integrable hm 0)
  rw [hSL,hmean] at h1
  rw [exp_tail_integral hm L,exp_tail_integral hm 0] at h2
  simp at h2
  linarith [mul_pos hm (exp_pos (-L/m))]

end BetaIFR
end

section
open Filter Set MeasureTheory Real
open scoped ENNReal Topology

namespace BetaIFR

/-- A single crossing concentrates probability in every open interval containing the cutoff. -/
theorem central_mass {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {c : ℝ} (hleft : ∀ x ∈ Ioo 0 c, Q (Ioi x) ≤ P (Ioi x))
    (hright : ∀ x, c < x → P (Ioi x) ≤ Q (Ioi x))
    {U : Set ℝ} (ho : IsOpen U) (hv : Convex ℝ U) (hc : c ∈ U) (hp : U ⊆ Ioi 0) :
    Q U ≤ P U := by
  rw [ho.measure_eq_iSup_isCompact Q]
  refine iSup_le fun K ↦ iSup_le fun hKU ↦ iSup_le fun hK ↦ ?_
  let J := insert c K
  have hJ : IsCompact J := hK.insert c
  have hJU : J ⊆ U := insert_subset hc hKU
  have hn : J.Nonempty := ⟨c, mem_insert _ _⟩
  obtain ⟨l, hl⟩ := hJ.exists_isLeast hn
  obtain ⟨r, hr⟩ := hJ.exists_isGreatest hn
  obtain ⟨l', u', hlu, hU'⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds (hJU hl.1))
  obtain ⟨a, hla, hal⟩ := exists_between hlu.1
  have ha := hU' ⟨hla, hal.trans hlu.2⟩
  obtain ⟨l'', u'', hlu', hU''⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds (hJU hr.1))
  obtain ⟨b, hrb, hbu⟩ := exists_between hlu'.2
  have hb := hU'' ⟨hlu'.1.trans hrb, hbu⟩
  have hac := hal.trans_le (hl.2 (mem_insert c K))
  have hcb := (hr.2 (mem_insert c K)).trans_lt hrb
  have hsub := Ioi_subset_Ioi (hac.trans hcb).le
  calc Q K ≤ Q (Ioc a b) := measure_mono fun x hx ↦
         ⟨hal.trans_le (hl.2 (mem_insert_of_mem _ hx)), ((hr.2 (mem_insert_of_mem _ hx)).trans hrb.le)⟩
       _ ≤ P (Ioc a b) := by
         rw [← Ioi_sdiff_Ioi, measure_sdiff hsub measurableSet_Ioi.nullMeasurableSet (by finiteness),
           measure_sdiff hsub measurableSet_Ioi.nullMeasurableSet (by finiteness)]
         exact tsub_le_tsub (hleft a ⟨hp ha,hac⟩) (hright b hcb)
       _ ≤ P U := measure_mono ((Ioc_subset_Icc_self).trans (hv.ordConnected.out ha hb))

/-- Remove a supporting affine function at the cutoff. Positive strict sublevel sets of the
remaining nonnegative convex function are central intervals. -/
theorem convex_expectation_of_crossing {P Q : Measure ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : ∀ᵐ x ∂P, 0 < x) (hQ : ∀ᵐ x ∂Q, 0 < x)
    (iP : Integrable id P) (iQ : Integrable id Q)
    (hm : (∫ x, x ∂P) = ∫ x, x ∂Q) {c : ℝ} (hc : 0 < c)
    (hl : ∀ x ∈ Ioo 0 c, Q (Ioi x) ≤ P (Ioi x))
    (hr : ∀ x, c < x → P (Ioi x) ≤ Q (Ioi x))
    {φ : ℝ → ℝ} (hv : ConvexOn ℝ (Ioi 0) φ) (hφ : Measurable φ) (iφ : Integrable φ Q) :
    Integrable φ P ∧ (∫ x, φ x ∂P) ≤ ∫ x, φ x ∂Q := by
  let k := derivWithin φ (Ioi c) c
  let d := k * c - φ c
  let g := fun x ↦ φ x - k * x + d
  have hg : Measurable g := (hφ.sub (measurable_const.mul measurable_id)).add measurable_const
  have hc' : c ∈ interior (Ioi (0 : ℝ)) := by rwa [isOpen_Ioi.interior_eq]
  have hn (x : ℝ) (hx : 0 < x) : 0 ≤ g x := by
    rcases lt_trichotomy x c with h | rfl | h
    · have hs := (hv.slope_le_leftDeriv_of_mem_interior hx hc' h).trans
        (hv.leftDeriv_le_rightDeriv_of_mem_interior hc')
      rw [slope_def_field] at hs
      change _ ≤ k at hs
      have := (div_le_iff₀ (sub_pos.mpr h)).mp hs
      dsimp [g,d]; linarith
    · dsimp [g,d]; ring_nf; rfl
    · have hs := hv.rightDeriv_le_slope_of_mem_interior hc' hx h
      rw [slope_def_field] at hs
      change k ≤ _ at hs
      have := (le_div_iff₀ (sub_pos.mpr h)).mp hs
      dsimp [g,d]; linarith
  have gv : ConvexOn ℝ (Ioi 0) g :=
    (hv.sub ((LinearMap.mul ℝ ℝ k).concaveOn (convex_Ioi 0))).add_const d
  have hnp := hP.mono hn
  have hnq := hQ.mono hn
  have hmass (t : ℝ) (ht : 0 < t) : P {x | t ≤ g x} ≤ Q {x | t ≤ g x} := by
    let U := {x ∈ Ioi 0 | g x < t}
    have ho : IsOpen U := (gv.continuousOn isOpen_Ioi).isOpen_inter_preimage isOpen_Ioi isOpen_Iio
    have hcu : c ∈ U := ⟨hc, by dsimp [g,d]; linarith⟩
    have hle := central_mass hl hr ho (gv.convex_lt t) hcu fun _ hx ↦ hx.1
    have heq (M : Measure ℝ) (hM : ∀ᵐ x ∂M, 0 < x) : M {x | t ≤ g x} = M Uᶜ := by
      apply measure_congr
      filter_upwards [hM] with x hx
      apply propext
      change (t ≤ g x) ↔ ¬(0 < x ∧ g x < t)
      simp [hx]
    rw [heq P hP,heq Q hQ,prob_compl_eq_one_sub ho.measurableSet,prob_compl_eq_one_sub ho.measurableSet]
    exact tsub_le_tsub_left hle _
  have hle : (∫⁻ x, ENNReal.ofReal (g x) ∂P) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂Q := by
    rw [lintegral_eq_lintegral_meas_le P hnp hg.aemeasurable,
      lintegral_eq_lintegral_meas_le Q hnq hg.aemeasurable]
    exact setLIntegral_mono' measurableSet_Ioi hmass
  have igQ : Integrable g Q := (iφ.sub (iQ.const_mul k)).add (integrable_const d)
  have igP : Integrable g P := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnp]
    exact hle.trans_lt igQ.lintegral_lt_top
  have iphi : Integrable φ P := by
    have h := (igP.add (iP.const_mul k)).sub (integrable_const d)
    convert h using 1
    ext x
    dsimp [g]; ring
  refine ⟨iphi, ?_⟩
  have comp : (∫ x, g x ∂P) ≤ ∫ x, g x ∂Q := by
    rw [integral_eq_lintegral_of_nonneg_ae hnp hg.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae hnq hg.aestronglyMeasurable]
    exact ENNReal.toReal_mono igQ.lintegral_lt_top.ne hle
  have eqn (M : Measure ℝ) [IsProbabilityMeasure M] (im : Integrable id M) (ih : Integrable φ M) :
      (∫ x, g x ∂M) = (∫ x, φ x ∂M) - k * (∫ x, x ∂M) + d := by
    have ik : Integrable (fun x : ℝ ↦ k * x) M := im.const_mul k
    have isub : Integrable (fun x ↦ φ x - k * x) M := ih.sub ik
    dsimp only [g]
    rw [integral_add isub (integrable_const d),integral_sub ih ik,integral_const_mul]
    simp
  rw [eqn P iP iphi,eqn Q iQ iφ,hm] at comp
  linarith

end BetaIFR
end

section
open MeasureTheory Set Filter
open scoped ENNReal

namespace BetaIFR

noncomputable def densityLaw (A : Set ℝ) (w : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict A).withDensity (fun x ↦ ENNReal.ofReal (w x))

theorem density_integral {A : Set ℝ} {w : ℝ → ℝ} (hw : AEMeasurable w (volume.restrict A))
    (hn : 0 ≤ᵐ[volume.restrict A] w) (f : ℝ → ℝ) :
    (∫ x, f x ∂densityLaw A w) = ∫ x in A, f x * w x := by
  rw [densityLaw,integral_withDensity_eq_integral_toReal_smul₀ hw.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  simp [ENNReal.toReal_ofReal hx, mul_comm]

theorem density_integrable {A : Set ℝ} {w f : ℝ → ℝ} (hw : AEMeasurable w (volume.restrict A))
    (hn : 0 ≤ᵐ[volume.restrict A] w) :
    Integrable f (densityLaw A w) ↔ IntegrableOn (fun x ↦ f x * w x) A := by
  rw [densityLaw,integrable_withDensity_iff_integrable_smul₀' hw.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [hn] with x hx
  simp [ENNReal.toReal_ofReal hx,mul_comm]

theorem density_probability {A : Set ℝ} {w : ℝ → ℝ} (hn : 0 ≤ᵐ[volume.restrict A] w)
    (h1 : (∫ x in A, w x) = 1) : IsProbabilityMeasure (densityLaw A w) := by
  have hi : IntegrableOn w A := Integrable.of_integral_ne_zero (h1.trans_ne one_ne_zero)
  constructor
  rw [densityLaw,withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn,h1,ENNReal.ofReal_one]

theorem density_mem {A : Set ℝ} (hA : MeasurableSet A) (w : ℝ → ℝ) :
    ∀ᵐ x ∂densityLaw A w, x ∈ A :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hA)

end BetaIFR
end

section
open Filter Set MeasureTheory ProbabilityTheory Real
open scoped ENNReal Topology

namespace BetaIFR

theorem exp_survival {m : ℝ} (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) :
    (expMeasure m⁻¹).real (Ioi x) = exp (-x / m) := by
  have := isProbabilityMeasure_expMeasure (inv_pos.mpr hm)
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
    cdf_expMeasure_eq (inv_pos.mpr hm),if_pos hx]
  ring_nf

theorem exp_positive {m : ℝ} (hm : 0 < m) : ∀ᵐ x ∂expMeasure m⁻¹, 0 < x := by
  have := isProbabilityMeasure_expMeasure (inv_pos.mpr hm)
  apply (mem_ae_iff_prob_eq_one (measurableSet_Ioi (a := (0 : ℝ)))).mpr
  have h := exp_survival hm (x := 0) le_rfl
  simpa [Measure.real, ENNReal.toReal_eq_one_iff] using h

/-- Identify mathlib's exponential probability with its Lebesgue density. -/
theorem exp_eq_density {m : ℝ} :
    expMeasure m⁻¹ = densityLaw (Ici 0) (fun x ↦ m⁻¹ * exp (-x / m)) := by
  change volume.withDensity (exponentialPDF m⁻¹) = _
  rw [densityLaw, ← withDensity_indicator measurableSet_Ici]
  congr 1
  ext x
  rw [exponentialPDF_eq]
  by_cases hx : 0 ≤ x <;> simp [hx, div_eq_inv_mul]

theorem exp_integral {m : ℝ} (hm : 0 < m) (f : ℝ → ℝ) :
    (∫ x, f x ∂expMeasure m⁻¹) = ∫ x in Ioi 0, f x * (m⁻¹ * exp (-x / m)) := by
  rw [exp_eq_density, density_integral (by fun_prop) (ae_of_all _ fun x ↦ by positivity),
    integral_Ici_eq_integral_Ioi]

theorem exp_integrable {m : ℝ} (hm : 0 < m) (f : ℝ → ℝ) :
    Integrable f (expMeasure m⁻¹) ↔ IntegrableOn (fun x ↦ f x * (m⁻¹ * exp (-x / m))) (Ioi 0) := by
  rw [exp_eq_density,density_integrable (by fun_prop) (ae_of_all _ fun x ↦ by positivity),
    integrableOn_Ici_iff_integrableOn_Ioi]

theorem exp_mean {m : ℝ} (hm : 0 < m) : (∫ x, x ∂expMeasure m⁻¹) = m := by
  rw [exp_integral hm]
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) (inv_pos.mpr hm)
  norm_num at h
  simp_rw [show ∀ x : ℝ, x * (m⁻¹ * exp (-x/m)) = m⁻¹ * (x * exp (-(m⁻¹*x))) by
    intro x; rw [neg_div,div_eq_inv_mul]; ring,integral_const_mul]
  rw [h]
  field_simp

theorem exp_half_moment {m : ℝ} (hm : 0 < m) :
    Integrable (fun x ↦ exp (x/(2*m))) (expMeasure m⁻¹) ∧
    (∫ x, exp (x / (2*m)) ∂expMeasure m⁻¹) = 2 := by
  rw [exp_integral hm,exp_integrable hm]
  exact BetaExponential.expMoment hm

theorem exp_neg_log_moment {m : ℝ} (hm : 0 < m) :
    Integrable (fun x ↦ -log x) (expMeasure m⁻¹) ∧
    (∫ x, -log x ∂expMeasure m⁻¹) = eulerMascheroniConstant - log m := by
  rw [exp_integral hm,exp_integrable hm]
  exact BetaExponential.logMoment hm

theorem euler_lt_log_nine_fourths : eulerMascheroniConstant < log (9/4) := by
  calc eulerMascheroniConstant < 2 / 3 := eulerMascheroniConstant_lt_two_thirds
       _ < log 2 := by linarith [log_two_gt_d9]
       _ < _ := log_lt_log (by norm_num) (by norm_num)

end BetaIFR
end

section
open Set Filter MeasureTheory ProbabilityTheory Real
open scoped ENNReal Topology

namespace BetaIFR

/-- A probability on (0,L] with positive log-concave survival on [0,L) is below the
exponential of its own mean in convex order. -/
theorem ifr_convex_order {P : Measure ℝ} [IsProbabilityMeasure P] {L m : ℝ}
    (hL : 0 < L) (hm : 0 < m) (hP : ∀ᵐ x ∂P, 0 < x) (hme : (∫ x, x ∂P) = m)
    (hpos : ∀ x ∈ Ico 0 L, 0 < P.real (Ioi x)) (hend : P (Ioi L) = 0)
    (hlog : ConcaveOn ℝ (Ico 0 L) (fun x ↦ log (P.real (Ioi x))))
    {φ : ℝ → ℝ} (hv : ConvexOn ℝ (Ioi 0) φ) (hφ : Measurable φ)
    (iφ : Integrable φ (expMeasure m⁻¹)) :
    Integrable φ P ∧ (∫ x, φ x ∂P) ≤ ∫ x, φ x ∂expMeasure m⁻¹ := by
  let S : ℝ → ℝ := fun x ↦ P.real (Ioi x)
  have hi : Integrable id P := Integrable.of_integral_ne_zero (hme.trans_ne hm.ne')
  have hQ := isProbabilityMeasure_expMeasure (inv_pos.mpr hm)
  have hQm := exp_mean hm
  have him : Integrable id (expMeasure m⁻¹) := Integrable.of_integral_ne_zero (hQm.trans_ne hm.ne')
  have h0 : S 0 = 1 := by
    have := (mem_ae_iff_prob_eq_one (μ := P) measurableSet_Ioi).mp hP
    simpa [S,Measure.real,ENNReal.toReal_eq_one_iff] using this
  have hfin (x : ℝ) (hx : L ≤ x) : S x = 0 := by
    simp [S,Measure.real, measure_mono_null (Ioi_subset_Ioi hx) hend]
  have harea : (∫ x in Ioi 0, S x) = m := by
    have he := hi.integral_eq_integral_meas_lt (hP.mono fun _ hx ↦ hx.le)
    exact he.symm.trans hme
  have hiS : IntegrableOn S (Ioi 0) := Integrable.of_integral_ne_zero (harea.trans_ne hm.ne')
  obtain ⟨c,hc,hl,hr⟩ := survival_crossing (m := m) hL h0 hpos hfin hlog
  have hcpos := crossing_pos hm hL hc.1 (fun x hx ↦ (hr x hx).le) hfin hiS harea
  refine convex_expectation_of_crossing hP (exp_positive hm) hi him (hme.trans hQm.symm)
    hcpos ?_ ?_ hv hφ iφ
  · intro x hx
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    change (expMeasure m⁻¹).real (Ioi x) ≤ S x
    rw [exp_survival hm hx.1.le]
    exact hl x hx
  · intro x hx
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    change S x ≤ (expMeasure m⁻¹).real (Ioi x)
    rw [exp_survival hm (hcpos.trans hx).le]
    exact (hr x hx).le

theorem ifr_moments {P : Measure ℝ} [IsProbabilityMeasure P] {L m : ℝ}
    (hL : 0 < L) (hm : 0 < m) (hP : ∀ᵐ x ∂P, 0 < x) (hme : (∫ x, x ∂P) = m)
    (hpos : ∀ x ∈ Ico 0 L, 0 < P.real (Ioi x)) (hend : P (Ioi L) = 0)
    (hlog : ConcaveOn ℝ (Ico 0 L) (fun x ↦ log (P.real (Ioi x)))) :
    (Integrable (fun x ↦ -log x) P ∧ (∫ x, -log x ∂P) ≤ eulerMascheroniConstant - log m) ∧
    (Integrable (fun x ↦ exp (x/(2*m))) P ∧ (∫ x, exp (x/(2*m)) ∂P) ≤ 2) := by
  have hl := exp_neg_log_moment hm
  have hg := exp_half_moment hm
  have h1 := ifr_convex_order hL hm hP hme hpos hend hlog
    strictConcaveOn_log_Ioi.concaveOn.neg (by fun_prop) hl.1
  have hv : ConvexOn ℝ (Ioi 0) (fun x ↦ exp (x / (2*m))) := by
    have he := convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ (2*m)⁻¹)
    exact (he.subset (by simp) (convex_Ioi 0)).congr fun x _ ↦ by
      simp [div_eq_inv_mul]
  have h2 := ifr_convex_order hL hm hP hme hpos hend hlog hv (by fun_prop) hg.1
  exact ⟨⟨h1.1,h1.2.trans_eq hl.2⟩,⟨h2.1,h2.2.trans_eq hg.2⟩⟩

end BetaIFR
end

section
open Set Filter MeasureTheory Real
open scoped ENNReal Topology

namespace BetaIFR

/-- For the finite-interval density, Lean's real-valued tail measure is the ordinary tail integral. -/
theorem density_tail {f : ℝ → ℝ} {L x : ℝ}
    (hf : ContinuousOn f (Icc 0 L)) (hn : ∀ y ∈ Icc 0 L, 0 ≤ f y)
    (hx : x ∈ Icc 0 L) :
    (densityLaw (Ioc 0 L) f).real (Ioi x) = ∫ y in x..L, f y := by
  rw [Measure.real, densityLaw,withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,inter_comm,Ioc_inter_Ioi,sup_eq_right.mpr hx.1,
    intervalIntegral.integral_of_le hx.2]
  symm
  apply integral_eq_lintegral_of_nonneg_ae
  · exact (ae_restrict_mem measurableSet_Ioc).mono fun y hy ↦ hn y ⟨hx.1.trans hy.1.le,hy.2⟩
  · exact (hf.mono fun y hy ↦ ⟨hx.1.trans hy.1.le,hy.2⟩).aestronglyMeasurable measurableSet_Ioc

/-- The two moment bounds as interval integrals. Both integrability assertions are proved,
including at the logarithmic singularity at zero. -/
theorem density_moments {f : ℝ → ℝ} {L m : ℝ} (hL : 0 < L) (hm : 0 < m)
    (hf : ContinuousOn f (Icc 0 L)) (hn : ∀ x ∈ Icc 0 L, 0 ≤ f x)
    (h1 : (∫ x in 0..L, f x) = 1) (hme : (∫ x in 0..L, x * f x) = m)
    (hpos : ∀ x ∈ Ico 0 L, 0 < ∫ y in x..L, f y)
    (hlog : ConcaveOn ℝ (Ico 0 L) (fun x ↦ log (∫ y in x..L, f y))) :
    (IntervalIntegrable (fun x ↦ (-log x) * f x) volume 0 L ∧
      (∫ x in 0..L, (-log x) * f x) ≤ eulerMascheroniConstant - log m) ∧
    (IntervalIntegrable (fun x ↦ exp (x/(2*m)) * f x) volume 0 L ∧
      (∫ x in 0..L, exp (x/(2*m)) * f x) ≤ 2) := by
  let P := densityLaw (Ioc 0 L) f
  have hae : 0 ≤ᵐ[volume.restrict (Ioc 0 L)] f := (ae_restrict_mem measurableSet_Ioc).mono
    fun x hx ↦ hn x ⟨hx.1.le,hx.2⟩
  have hmeas : AEMeasurable f (volume.restrict (Ioc 0 L)) := ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc).aemeasurable
  rw [intervalIntegral.integral_of_le hL.le] at h1 hme
  have hi : IsProbabilityMeasure P := density_probability hae h1
  have hmem : ∀ᵐ x ∂P, x ∈ Ioc 0 L := density_mem measurableSet_Ioc f
  have hp : P (Ioi L) = 0 := by
    simpa only [not_le, Ioi] using (ae_iff.mp (hmem.mono fun x hx ↦ hx.2))
  have hs (x : ℝ) (hx : x ∈ Ico 0 L) : P.real (Ioi x) = ∫ y in x..L, f y :=
    density_tail hf hn ⟨hx.1,hx.2.le⟩
  have hg := ifr_moments hL hm (hmem.mono fun _ hx ↦ hx.1)
    ((density_integral hmeas hae id).trans hme) (fun x hx ↦ (hs x hx).symm ▸ hpos x hx) hp
    (hlog.congr fun x hx ↦ congrArg log (hs x hx).symm)
  simp only [intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le,intervalIntegral.integral_of_le hL.le]
  exact ⟨⟨(density_integrable hmeas hae).mp hg.1.1, (density_integral hmeas hae _).symm.le.trans hg.1.2⟩,
    ⟨(density_integrable hmeas hae).mp hg.2.1, (density_integral hmeas hae _).symm.le.trans hg.2.2⟩⟩

end BetaIFR
end

section
open Set MeasureTheory Real OMA.S_mo_403324
namespace MO403324Glue

theorem final :
    type_of% @OMA.S_mo_403324.main := by
  intro n k p hk hn hp
  have hk' : 0 < k := by omega
  have hm := mean_pos n k p hk' hn hp
  have hn0 (z : ℝ) (_hz : z ∈ Icc (0:ℝ) 1) : 0 ≤ density n k p z := by
    exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hp.le) (excess_pos p hn hp).le)
      (ProbabilityTheory.cdf_nonneg _ _)
  have hpos (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) : 0 < ∫ z in x..1, density n k p z := by
    change 0 < ∫ z in x..1, BetaNormalization.markedDensity n k p z
    rw [BetaNormalization.marked_survival n k p hk' hn ⟨hx.1,hx.2.le⟩]
    exact div_pos (BetaNormalization.excess_positive hn ⟨mul_pos hp (sub_pos.mpr hx.2),
      (mul_le_mul_of_nonneg_right p.2.2 (sub_nonneg.mpr hx.2.le)).trans (by linarith [hx.1])⟩)
      (excess_pos p hn hp)
  have moments := BetaIFR.density_moments (by norm_num : (0:ℝ) < 1) hm
    (density_continuousOn n k p hk' hn) hn0 (density_norm n k p hk' hn hp) rfl hpos
    (BetaNormalization.marked_survival_concave n k p hk' hn hp)
  exact source_conditional n k p hk' hn hp moments.1.2 moments.2.2

end MO403324Glue
end

section
theorem OMA.solution : type_of% @OMA.S_mo_403324.main :=
  MO403324Glue.final
end
