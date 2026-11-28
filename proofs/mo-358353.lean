import OMAStatements.S_mo_358353

/-!
The proof follows Clément Canonne's chi-squared calculation at
https://mathoverflow.net/a/358535. The reference measure in its denominator
is the unperturbed Poisson law, which has strictly positive mass at every index.
-/

namespace OMA.S_mo_358353
open ProbabilityTheory Real
open scoped NNReal

private lemma mass_formula (r : ℝ≥0) (n : ℕ) :
    mass r n = exp (-r) * (r:ℝ)^n / n.factorial := poissonMeasure_real_singleton r n

private lemma mass_sum (r : ℝ≥0) : HasSum (mass r) 1 := by
  change HasSum (fun n => mass r n) 1
  simpa only [mass_formula] using hasSum_one_poissonMeasure r

private lemma mix_sum (r a : ℝ≥0) : HasSum (mixture r a) 1 := by
  change HasSum (fun n => mixture r a n) 1
  simpa [mixture] using (((mass_sum ((1+a)*r)).add (mass_sum ((1-a)*r))).div_const 2)

private lemma mixed_moment (A B r : ℝ≥0) (hr : 0 < r) :
    HasSum (fun n => mass A n * mass B n / mass r n)
      (exp ((A:ℝ)*B/r - A - B + r)) := by
  let z : ℝ≥0 := A * B / r
  have hz : (z:ℝ) = (A:ℝ)*B/r := by simp [z]
  have hh := (mass_sum z).mul_left (exp ((A:ℝ)*B/r - A - B + r))
  rw [mul_one] at hh
  apply hh.congr_fun
  intro n
  simp only [mass_formula, hz, div_pow, mul_pow]
  have he : exp ((A:ℝ)*B/r - A - B + r) * exp (-((A:ℝ)*B/r)) * exp (-(r:ℝ)) =
      exp (-(A:ℝ)) * exp (-(B:ℝ)) := by
    simp only [← exp_add]
    congr 1
    ring
  have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hf : (n.factorial:ℝ) ≠ 0 := by positivity
  generalize exp ((A:ℝ)*B/r - A - B + r) = k at he ⊢
  field_simp [ne_of_gt (exp_pos _), hr', hf]
  linear_combination -((A:ℝ)^n * (B:ℝ)^n) * he

private lemma second_moment (r a : ℝ≥0) (hr : 0 < r) (ha : a ≤ 1) :
    HasSum (fun n => (mixture r a n)^2 / mass r n) (cosh ((a:ℝ)^2*r)) := by
  let A := (1+a)*r
  let B := (1-a)*r
  let x : ℝ := (a:ℝ)^2*r
  have hA : (A:ℝ) = (1+(a:ℝ))*r := by simp [A]
  have hB : (B:ℝ) = (1-(a:ℝ))*r := by simp [B, NNReal.coe_sub ha]
  have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hAA : (A:ℝ)*A/r-A-A+r = x := by rw [hA]; dsimp [x]; field_simp; ring
  have hBB : (B:ℝ)*B/r-B-B+r = x := by rw [hB]; dsimp [x]; field_simp; ring
  have hAB : (A:ℝ)*B/r-A-B+r = -x := by rw [hA,hB]; dsimp [x]; field_simp; ring
  have h1 := mixed_moment A A r hr
  have h2 := mixed_moment B B r hr
  have h3 := mixed_moment A B r hr
  rw [hAA] at h1
  rw [hBB] at h2
  rw [hAB] at h3
  have h := ((h1.add h2).add (h3.mul_left 2)).div_const 4
  convert! h using 1
  · funext n
    change ((mass A n+mass B n)/2)^2 / mass r n = _
    ring
  · change cosh x = _
    rw [Real.cosh_eq]
    ring

private lemma chi_square (r a : ℝ≥0) (hr : 0 < r) (ha : a ≤ 1) :
    HasSum (fun n => (mixture r a n-mass r n)^2 / mass r n) (cosh ((a:ℝ)^2*r)-1) := by
  have h := ((second_moment r a hr ha).sub ((mix_sum r a).mul_left 2)).add (mass_sum r)
  convert! h using 1
  · funext n
    have hp := poissonMeasure_real_singleton_pos n hr
    change 0 < mass r n at hp
    field_simp [hp.ne']
    ring
  · ring

private lemma pointwise_hellinger {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    (sqrt p-sqrt q)^2 ≤ (q-p)^2/p := by
  rw [le_div_iff₀ hp]
  have hs : 0 ≤ (sqrt p-sqrt q)^2 * ((sqrt p+sqrt q)^2-p) := by
    apply mul_nonneg (sq_nonneg _)
    nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hq, mul_nonneg (sqrt_nonneg p) (sqrt_nonneg q)]
  have h : q-p = (sqrt q-sqrt p)*(sqrt q+sqrt p) := by
    nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hq]
  rw [h]
  nlinarith [hs]

private lemma cosh_bound {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) : cosh x - 1 ≤ x^2 := by
  have h := Real.norm_exp_sub_one_sub_id_le (x := x) (by simpa [Real.norm_eq_abs,abs_of_nonneg hx] using h1)
  have k := Real.norm_exp_sub_one_sub_id_le (x := -x) (by simpa [Real.norm_eq_abs,abs_of_nonneg hx] using h1)
  simp only [Real.norm_eq_abs, sq_abs, neg_sq] at h k
  rw [Real.cosh_eq]
  nlinarith [le_abs_self (exp x-1-x), le_abs_self (exp (-x)-1-(-x)),
    sq_abs x, sq_abs (-x)]

end OMA.S_mo_358353

open OMA.S_mo_358353

theorem OMA.solution : type_of% @OMA.S_mo_358353.main := by
  refine ⟨1, by norm_num, ?_⟩
  intro r a hr ha
  let x : ℝ := (a:ℝ)^2*r
  let d : ℕ → ℝ := fun n => (Real.sqrt (mass r n) - Real.sqrt (mixture r a n))^2
  have hd (n : ℕ) : 0 ≤ d n := sq_nonneg _
  have hp (n : ℕ) : 0 < mass r n := ProbabilityTheory.poissonMeasure_real_singleton_pos n hr
  have hq (n : ℕ) : 0 ≤ mixture r a n := by unfold mixture mass; positivity
  have hmaj (n : ℕ) : d n ≤ mass r n + mixture r a n := by
    dsimp [d]
    nlinarith [Real.sq_sqrt (hp n).le, Real.sq_sqrt (hq n),
      mul_nonneg (Real.sqrt_nonneg (mass r n)) (Real.sqrt_nonneg (mixture r a n))]
  have hsum := (mass_sum r).add (mix_sum r a)
  have hds : Summable d := Summable.of_nonneg_of_le hd hmaj hsum.summable
  simp only [one_mul]
  change Real.sqrt ((∑' n, d n)/2) ≤ x
  rw [Real.sqrt_le_iff]
  have hx : 0 ≤ x := by dsimp [x]; positivity
  refine ⟨hx, ?_⟩
  by_cases h1 : x ≤ 1
  · have hc := chi_square r a hr ha
    have he := hds.tsum_le_tsum (fun n => pointwise_hellinger (hp n) (hq n)) hc.summable
    rw [hc.tsum_eq] at he
    change ∑' n, d n ≤ Real.cosh x-1 at he
    nlinarith [cosh_bound hx h1, sq_nonneg x]
  · have he := hds.tsum_le_tsum hmaj hsum.summable
    rw [hsum.tsum_eq] at he
    nlinarith [sq_nonneg (x-1)]
