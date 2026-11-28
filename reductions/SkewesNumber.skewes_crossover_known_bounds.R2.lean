import FormalConjectures.Wikipedia.SkewesNumber
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The first Skewes crossover

The lower bound follows from the sign of θ(p) − p at primes above 100000.
Below that cutoff an integer certificate bounds primorials on 558 intervals.
The proof starts from the principal-value definition of li(2) and propagates a
strict bound on li − π − (x − θ(x))/log x. Büthe's estimate (1.7) in
*An analytic method for bounding ψ(x)* implies the remaining prime bounds.

For the upper bound we use the unconditional window in Lemma 9.3 of
Saouter, Trudgian and Demichel, *A still sharper region where π(x) − li(x) is
positive*. Positivity of their weighted integral suffices to give an integer
crossing below exp(727.95134).
-/

-- Reduction SkewesNumber.skewes_crossover_known_bounds.R2
-- Credit: @wtho704

namespace OMA.R_SkewesNumber_skewes_crossover_known_bounds_R2

open Real Set MeasureTheory

/-- Büthe's estimate for θ is needed only at the remaining primes. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 100000 < p → p ≤ 10 ^ 19 → Chebyshev.theta p ≤ p

/-- Positivity in the unconditional Gaussian window of Saouter, Trudgian and Demichel,
Lemma 9.3. The center, half-width and Gaussian parameter are exact rationals. -/
def H2 : Prop :=
  let ω : ℝ := 727951335426 / 1000000000
  let η : ℝ := 47 / 69000000
  let α : ℝ := 161 * 10^13
  let w := fun t : ℝ => Real.sqrt (α / (2 * Real.pi)) * Real.exp (-α * (t-ω)^2 / 2) * t /
    (Real.exp (t / 2) * (1 + 2 / t + (251/25) / t^2))
  0 < ∫ t in (ω-η)..(ω+η), w t * ((Nat.primeCounting ⌊Real.exp t⌋₊ : ℝ) - Real.logIntegral (Real.exp t))

lemma positive_from_zero {f f' : ℝ → ℝ} (hf : f 0 = 0)
    (hd : ∀ x : ℝ, 0 ≤ x → x < 1 → HasDerivAt f (f' x) x)
    (hp : ∀ x : ℝ, 0 < x → x < 1 → 0 < f' x) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    0 < f u := by
  have mono : StrictMonoOn f (Icc 0 u) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 u)
    · intro x hx
      exact (hd x hx.1 (hx.2.trans_lt hu1)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x hx.1.le (hx.2.trans hu1)).deriv]
      exact hp x hx.1 (hx.2.trans hu1)
  simpa [hf] using mono (left_mem_Icc.mpr hu.le) (right_mem_Icc.mpr hu.le) hu

/-- Two successive derivatives reduce the bound on the principal-value integrand to log(1-u²)<0. -/
lemma integrand_gt_one {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    1 < 1 / log (1 + u) + 1 / log (1 - u) := by
  let H := fun x : ℝ => 2*x - (1+x)*log (1+x) + (1-x)*log (1-x)
  let G := fun x : ℝ => (1 - log (1 + x)) * (-log (1 - x)) - log (1 + x)
  have plus (x : ℝ) : HasDerivAt (fun t : ℝ => 1+t) 1 x := by simpa using (hasDerivAt_id x).const_add 1
  have minus (x : ℝ) : HasDerivAt (fun t : ℝ => 1-t) (-1) x := by simpa using (hasDerivAt_id x).const_sub 1
  have dh (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) : HasDerivAt H (-(log (1+x) + log (1-x))) x := by
    have a : 1+x ≠ 0 := by linarith
    have b : 1-x ≠ 0 := by linarith
    have d := (((hasDerivAt_id x).const_mul 2).sub ((plus x).mul ((plus x).log a))).add
      ((minus x).mul ((minus x).log b))
    convert d using 1 <;> try rfl
    all_goals field_simp [a,b]
    all_goals ring
  have hpos {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : 0 < H x := by
    apply positive_from_zero (f' := fun t => -(log (1+t) + log (1-t))) (by simp [H]) dh _ hx hx1
    intro t ht ht1
    rw [← Real.log_mul (by linarith : 1+t ≠ 0) (by linarith : 1-t ≠ 0)]
    exact neg_pos.mpr (Real.log_neg (mul_pos (by linarith) (by linarith)) (by nlinarith))
  have dg (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) : HasDerivAt G (H x / ((1+x)*(1-x))) x := by
    have a : 1+x ≠ 0 := by linarith
    have b : 1-x ≠ 0 := by linarith
    have d := ((((plus x).log a).const_sub 1).mul (((minus x).log b).neg)).sub ((plus x).log a)
    convert d using 1 <;> try rfl
    all_goals try dsimp [G, H]
    all_goals field_simp [a,b]
    all_goals ring
  have hg : 0 < G u := positive_from_zero (f' := fun t => H t / ((1+t)*(1-t)))
    (by simp [G]) dg (fun x hx hx1 => div_pos (hpos hx hx1) (mul_pos (by linarith) (by linarith))) hu hu1
  have a : 0 < log (1+u) := Real.log_pos (by linarith)
  have b : log (1-u) < 0 := Real.log_neg (by linarith) (by linarith)
  rw [div_add_div _ _ a.ne' b.ne, lt_div_iff_of_neg (mul_neg_of_pos_of_neg a b)]
  dsimp [G] at hg
  linarith

theorem li_two_gt_one : 1 < Real.logIntegral 2 := by
  let f := fun u : ℝ => 1 / log (1+u) + 1 / log (1-u)
  let S : Set ℝ := Ioo 0 1
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) S := integrableOn_const (hs := by simp [S]) (hC := by simp)
  have hf : IntegrableOn f S := Real.logIntegralTwo_integrand_integrableOn
  have hg : IntegrableOn (fun u => f u - 1) S := hf.sub hc
  have hpos (x : ℝ) (hx : x ∈ S) : 0 < f x - 1 := sub_pos.mpr (integrand_gt_one hx.1 hx.2)
  have ae : 0 ≤ᵐ[volume.restrict S] (fun u => f u - 1) := by
    filter_upwards [ae_restrict_mem (μ := volume) (show MeasurableSet S from measurableSet_Ioo)] with x hx
    exact (hpos x hx).le
  have hsupp : Function.support (fun u => f u - 1) ∩ S = S :=
    Set.inter_eq_right.mpr fun x hx => (hpos x hx).ne'
  have hi : 0 < ∫ x in S, (f x - 1) := (setIntegral_pos_iff_support_of_nonneg_ae ae hg).2 (by
    rw [hsupp]; norm_num [S, Real.volume_Ioo])
  rw [integral_sub hf hc] at hi
  simpa [Real.logIntegral_two, Real.logIntegralTwo, S, f, Real.volume_real_Ioo] using hi

lemma inv_log_integrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / log t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro t ht
  exact (continuousAt_const.div (Real.continuousAt_log (by linarith [ht.1]))
    (Real.log_pos (by linarith [ht.1])).ne').continuousWithinAt

lemma li_diff {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    Real.logIntegral b - Real.logIntegral a = ∫ t in a..b, 1 / log t := by
  unfold Real.logIntegral
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left (inv_log_integrable (by norm_num) (ha.trans hab))
    (inv_log_integrable (by norm_num) ha)

lemma li_mono {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) : Real.logIntegral a ≤ Real.logIntegral b := by
  apply sub_nonneg.mp
  rw [li_diff ha hab]
  exact intervalIntegral.integral_nonneg hab fun t ht => div_nonneg zero_le_one (Real.log_nonneg (by linarith [ht.1]))

lemma li_step {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b-a) / log b ≤ Real.logIntegral b - Real.logIntegral a := by
  rw [li_diff ha hab]
  have hi := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (μ := volume) (c := 1 / log b))
    (inv_log_integrable (by linarith) hab) (fun t ht => by
      apply one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1]))
      exact Real.log_le_log (by linarith [ht.1]) ht.2)
  simpa [div_eq_mul_inv] using hi

lemma li_three_gt_two : 2 < Real.logIntegral 3 := by
  have hlog : log (5/2 : ℝ) < 1 := (Real.log_lt_iff_lt_exp (by norm_num)).2 (by linarith [Real.exp_one_gt_d9])
  have minor (t : ℝ) (ht : t ∈ Icc (2 : ℝ) 3) : 2-2/5*t ≤ 1 / log t := by
    have htpos : 0 < t := by linarith [ht.1]
    have logline := Real.log_le_sub_one_of_pos (show 0 < t / (5/2) by positivity)
    rw [Real.log_div htpos.ne' (by norm_num)] at logline
    have hlt : log t < 2/5*t := by linarith
    have hpos : 0 < log t := Real.log_pos (by linarith [ht.1])
    apply le_trans (show 2-2/5*t ≤ 2-log t by linarith)
    rw [le_div_iff₀ hpos]
    nlinarith [sq_nonneg (log t-1)]
  have hi := intervalIntegral.integral_mono_on (by norm_num : (2:ℝ) ≤ 3)
    ((continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    (inv_log_integrable (by norm_num) (by norm_num)) minor
  change (∫ t in (2 : ℝ)..3, (2-2/5*t)) ≤ (∫ t in (2 : ℝ)..3, 1 / log t) at hi
  have calcI : (∫ t in (2 : ℝ)..3, (2-2/5*t)) = 1 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (2 : ℝ)) (g := fun t : ℝ => (2/5)*t) intervalIntegrable_const ((continuous_const.mul continuous_id).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id]
    norm_num
  rw [calcI, ← li_diff (by norm_num) (by norm_num)] at hi
  linarith [li_two_gt_one]

/-- Integer upper bound on j^64 gives a rational lower bound on 1/log j. -/
lemma inv_log_credit {j h g : ℕ} (hj : 1 < j) (height : j^64 ≤ 2^h)
    (budget : g*(693148*h) ≤ 64000000000000) : (g:ℝ)/1000000 ≤ 1/log j := by
  have hjr : (1:ℝ) < j := by exact_mod_cast hj
  have hx : (j:ℝ)^64 ≤ (2:ℝ)^h := by exact_mod_cast height
  have hlog := Real.log_le_log (pow_pos (by linarith : (0:ℝ) < j) 64) hx
  rw [Real.log_pow, Real.log_pow] at hlog
  have h2 : log 2 ≤ 693148/1000000 := by linarith [Real.log_two_lt_d9]
  have hmul := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg h : (0:ℝ) ≤ h)
  have hk : 64*log j ≤ h*(693148/1000000) := by norm_num at hlog; linarith
  have hgb : (g:ℝ)*(693148*h) ≤ 64000000000000 := by exact_mod_cast budget
  have gain := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg g : (0:ℝ) ≤ g)
  rw [le_div_iff₀ (Real.log_pos hjr)]
  nlinarith only [gain, hgb]

lemma initial_values : (∀ n : ℕ, 2 ≤ n → n ≤ 32 → (Nat.primeCounting n : ℝ) < Real.logIntegral n) ∧
    13 < Real.logIntegral 32 := by
  let heights : List ℕ := [128,149,166,180,192,203,213,222,230,237,244,251,256,262,267,
    272,277,282,286,290,294,298,301,305,308,311,315,318,320]
  let gain := fun i : ℕ => 64000000000000 / (693148 * heights[i]?.getD 1)
  have heights_ok : ∀ i : Fin 29, (i.val+4)^64 ≤ 2^(heights[i.val]?.getD 1) := by decide +kernel
  have bounds (m : ℕ) (hm : m ≤ 29) :
      2 + ((∑ i ∈ Finset.range m, gain i : ℕ):ℝ)/1000000 < Real.logIntegral ((m:ℝ)+3) := by
    induction m with
    | zero => simpa using li_three_gt_two
    | succ m ih =>
      have hold := ih (by omega)
      have hk := inv_log_credit (g := gain m) (by omega : 1 < m + 4) (heights_ok ⟨m, by omega⟩)
        (Nat.div_mul_le_self ..)
      push_cast at hk
      have hstep := li_step (a := (m:ℝ)+3) (b := (m:ℝ)+4) (by have := Nat.cast_nonneg (α := ℝ) m; linarith) (by linarith)
      rw [show (m:ℝ)+4-(m+3)=1 by ring] at hstep
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_succ]
      rw [show (m:ℝ)+1+3=m+4 by ring]
      linarith
  have counts : ∀ k : Fin 30, 1000000 * Nat.primeCounting (k.val+3) ≤
      2000000 + ∑ i ∈ Finset.range k.val, gain i := by decide +kernel
  constructor
  · intro n hn hN
    by_cases he : n = 2
    · subst n
      have hπ : Nat.primeCounting 2 = 1 := by decide +kernel
      simpa [hπ] using li_two_gt_one
    · let k := n-3
      have kn : k+3 = n := by dsimp [k]; omega
      have hc := counts ⟨k, by omega⟩
      change 1000000 * Nat.primeCounting (k+3) ≤ 2000000 + ∑ i ∈ Finset.range k, gain i at hc
      rw [kn] at hc
      have hR : 1000000*(Nat.primeCounting n:ℝ) ≤ 2000000 + ((∑ i ∈ Finset.range k, gain i : ℕ):ℝ) := by exact_mod_cast hc
      have hb := bounds k (by omega)
      rw [show (k:ℝ)+3=(n:ℝ) by exact_mod_cast kn] at hb
      linarith
  · have hsum : 11000000 ≤ ∑ i ∈ Finset.range 29, gain i := by decide +kernel
    have hR : (11000000:ℝ) ≤ ((∑ i ∈ Finset.range 29, gain i : ℕ):ℝ) := by exact_mod_cast hsum
    have h := bounds 29 (by decide)
    norm_num only [Nat.cast_ofNat, show (29:ℝ)+3=32 by norm_num] at h
    linarith

/-- At 32 the logarithmic-integral surplus already absorbs the Chebyshev correction. -/
lemma seed_surplus : 0 < Real.logIntegral 32 - (Nat.primeCounting 32 : ℝ) -
    (32-Chebyshev.theta 32)/log 32 := by
  have hπ : Nat.primeCounting 32 = 11 := by decide +kernel
  have hP : 2 ^ 37 ≤ primorial 32 := by decide +kernel
  have hR : (2:ℝ)^37 ≤ (primorial 32 : ℝ) := by exact_mod_cast hP
  have ht := Real.log_le_log (by positivity) hR
  rw [Real.log_pow] at ht
  have hθ : Chebyshev.theta 32 = log (primorial 32 : ℝ) := by
    rw [Chebyshev.theta_eq_log_primorial]; norm_num
  have hl : log 32 = 5 * log 2 := calc
    log 32 = log ((2:ℝ)^5) := by norm_num
    _ = 5 * log 2 := by rw [Real.log_pow]; norm_num
  rw [hπ, hθ]
  have hpos : 0 < log 32 := Real.log_pos (by norm_num)
  have hcut : (32 - log (primorial 32 : ℝ)) / log 32 < 2 := by
    rw [div_lt_iff₀ hpos, hl]
    norm_num at ht
    linarith [Real.log_two_gt_d9]
  norm_num only [Nat.cast_ofNat]
  linarith [initial_values.2]

lemma theta_succ (n : ℕ) : Chebyshev.theta (n+1 : ℕ) = Chebyshev.theta n +
    if (n+1).Prime then log (n+1 : ℕ) else 0 := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_succ]
  split <;> simp_all [Finset.sum_insert, Nat.notMem_primesLE, add_comm]

lemma pi_succ (n : ℕ) : Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0) :=
  Nat.count_succ Nat.Prime (n+1)

/-- In a unit interval the prime jump cancels between π and θ/log. The remaining
term is nonnegative whenever θ(n) ≤ n. -/
lemma surplus_step (n : ℕ) (hn : 2 ≤ n) (ht : Chebyshev.theta n ≤ n) :
    Real.logIntegral n - (Nat.primeCounting n : ℝ) - ((n:ℝ)-Chebyshev.theta n)/log n ≤
    Real.logIntegral (n+1 : ℕ) - (Nat.primeCounting (n+1) : ℝ) -
      ((n+1:ℕ)-Chebyshev.theta (n+1 : ℕ))/log (n+1 : ℕ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 < log n := Real.log_pos (by linarith)
  have hl' : 0 < log (n+1:ℕ) := Real.log_pos (by exact_mod_cast (show 1 < n+1 by omega))
  have hstep := li_step (a := (n:ℝ)) (b := ((n+1:ℕ):ℝ)) hnR (by exact_mod_cast Nat.le_succ n)
  rw [show ((n+1:ℕ):ℝ)-n=1 by push_cast; ring] at hstep
  have hmono := Real.log_le_log (by linarith : (0:ℝ)<n) (by exact_mod_cast Nat.le_succ n : (n:ℝ) ≤ (n+1:ℕ))
  have hdiv := div_le_div_of_nonneg_left (sub_nonneg.mpr ht) hl hmono
  rw [pi_succ, theta_succ]
  by_cases hp : (n+1).Prime
  · simp only [hp, if_true, Nat.cast_add, Nat.cast_one] at *
    have heq : (n+1-(Chebyshev.theta n + log (n+1)))/log (n+1) =
        ((n:ℝ)-Chebyshev.theta n)/log (n+1) + 1/log (n+1) - 1 := by field_simp; ring
    rw [heq]
    linarith
  · simp only [hp, if_false, add_zero, Nat.cast_add, Nat.cast_one] at *
    have heq : ((n:ℝ)+1-Chebyshev.theta n)/log (n+1) =
        ((n:ℝ)-Chebyshev.theta n)/log (n+1) + 1/log (n+1) := by ring
    rw [heq]
    linarith

lemma pi_lt_li_of_theta (N : ℕ) (ht : ∀ n : ℕ, 32 ≤ n → n ≤ N → Chebyshev.theta n ≤ n) :
    ∀ n : ℕ, 2 ≤ n → n ≤ N → (Nat.primeCounting n : ℝ) < Real.logIntegral n := by
  have pos (k : ℕ) (hk : k+32 ≤ N) : 0 < Real.logIntegral (k+32:ℕ) - (Nat.primeCounting (k+32) : ℝ) -
      (((k+32:ℕ):ℝ)-Chebyshev.theta (k+32:ℕ))/log (k+32:ℕ) := by
    induction k with
    | zero => simpa using seed_surplus
    | succ k ih =>
      have h := (ih (by omega)).trans_le (surplus_step (k+32) (by omega) (ht _ (by omega) (by omega)))
      simpa only [show k+32+1 = k+1+32 by omega] using h
  intro n hn hN
  by_cases hsmall : n ≤ 32
  · exact initial_values.1 n hn hsmall
  · have hk := pos (n-32) (by omega)
    rw [show n-32+32=n by omega] at hk
    have hnon : 0 ≤ ((n:ℝ)-Chebyshev.theta n)/log n := div_nonneg (sub_nonneg.mpr (ht n (by omega) hN))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
    linarith

lemma primorial_increment (n : ℕ) : primorial (n+1) = primorial n * (if (n+1).Prime then n+1 else 1) := by
  rw [primorial_eq_prod_primesLE, Nat.primesLE_succ, primorial_eq_prod_primesLE]
  split <;> simp_all [Finset.prod_insert, Nat.notMem_primesLE, Nat.mul_comm]

/-- Product of primes in an interval is bounded by the product of any list which includes all of them. -/
lemma primorial_block (mark : ℕ → Bool) (covers : ∀ p : ℕ, p.Prime → mark p = true) (a k : ℕ) :
    primorial (a+k) ≤ primorial a * ((List.range' (a+1) k).filter mark).prod := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [List.range'_succ]
    have h := ih (a+1)
    rw [primorial_increment] at h
    rw [show a + (k + 1) = a + 1 + k by omega]
    refine h.trans ?_
    by_cases hp : (a+1).Prime
    · simp [hp, covers _ hp, Nat.mul_assoc]
    · by_cases hm : mark (a+1) = true
      · simp [hp, hm]
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (((List.range' (a+1+1) k).filter mark).prod)
          (Nat.le_mul_of_pos_right (primorial a) (Nat.succ_pos a))
      · simp [hp, hm]

lemma theta_from_power {p q u : ℕ} (hu : primorial p ^ 16 ≤ 2 ^ u)
    (hr : 693148*u ≤ 16000000*q) : Chebyshev.theta p ≤ q := by
  have h : (primorial p : ℝ)^16 ≤ (2:ℝ)^u := by exact_mod_cast hu
  have hp : 0 < (primorial p : ℝ) := by exact_mod_cast primorial_pos p
  have hl := Real.log_le_log (pow_pos hp 16) h
  rw [Real.log_pow, Real.log_pow] at hl
  have h2 : Real.log 2 ≤ 693148/1000000 := by linarith [Real.log_two_lt_d9]
  have hc := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg u : (0:ℝ) ≤ u)
  have hb : 693148*(u:ℝ) ≤ 16000000*(q:ℝ) := by exact_mod_cast hr
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  norm_num at hl
  linarith

/-- Each pair records an interval endpoint and an upper bound on the base-two logarithm
of its primorial, in sixteenths. All interval products and comparisons are checked as integers. -/
lemma certify_theta (mark : ℕ → Bool) (covers : ∀ p : ℕ, p.Prime → mark p = true)
    (valid : (ℕ × ℕ) × (ℕ × ℕ) → Bool)
    (spec : ∀ (a u b v : ℕ), valid ((a,u),(b,v)) = true →
      a ≤ b ∧ u ≤ v ∧ ((List.range' (a+1) (b-a)).filter mark).prod ^ 16 ≤ 2 ^ (v-u) ∧
        693148*v ≤ 16000000*a)
    (points : List (ℕ × ℕ)) (start : ℕ × ℕ)
    (hstart : primorial start.1 ^ 16 ≤ 2 ^ start.2)
    (check : (((start :: points).zip points).all valid) = true) :
    ∀ n : ℕ, start.1 < n → n ≤ (points.getLastD start).1 → Chebyshev.theta n ≤ n := by
  induction points generalizing start with
  | nil =>
    intro n hn hlast
    change n ≤ start.1 at hlast
    omega
  | cons next rest ih =>
    rw [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at check
    obtain ⟨hstep,htail⟩ := check
    obtain ⟨hab, huv, hprod, hbudget⟩ := spec _ _ _ _ hstep
    have hmul := primorial_block mark covers start.1 (next.1-start.1)
    rw [Nat.add_sub_of_le hab] at hmul
    have hp : primorial next.1 ^ 16 ≤ 2 ^ next.2 := calc
      _ ≤ (primorial start.1 * ((List.range' (start.1+1) (next.1-start.1)).filter mark).prod)^16 :=
        Nat.pow_le_pow_left hmul _
      _ ≤ 2 ^ start.2 * 2 ^ (next.2-start.2) := by rw [mul_pow]; exact Nat.mul_le_mul hstart hprod
      _ = _ := by rw [←pow_add, Nat.add_sub_of_le huv]
    intro n hn hlast
    by_cases h : n ≤ next.1
    · exact (Chebyshev.theta_mono (by exact_mod_cast h)).trans
        ((theta_from_power hp hbudget).trans (by exact_mod_cast hn.le))
    · apply ih next hp htail n (by omega)
      simpa only [List.getLastD_cons] using hlast

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
lemma theta_verified_range (n : ℕ) (hn : 1 < n) (hN : n ≤ 100000) : Chebyshev.theta n ≤ n := by
  -- Every prime survives the divisibility tests. Extra candidates only enlarge the product.
  let divisors : List ℕ := [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
    311, 313]
  let mark := fun j : ℕ => divisors.all (fun d => j % d != 0 || j == d)
  let valid := fun (s : (ℕ × ℕ) × (ℕ × ℕ)) =>
    let a := s.1.1
    let u := s.1.2
    let b := s.2.1
    let v := s.2.2
    decide (a ≤ b ∧ u ≤ v ∧ ((List.range' (a+1) (b-a)).filter mark).prod ^ 16 ≤ 2 ^ (v-u) ∧
      693148*v ≤ 16000000*a)
  have cover (p : ℕ) (hp : p.Prime) : mark p = true := by
    apply List.all_eq_true.mpr
    intro d hd
    have lower : divisors.all (fun j => 2 ≤ j) = true := by decide +kernel
    have hd2 : 2 ≤ d := by simpa using List.all_eq_true.mp lower d hd
    by_cases he : p = d
    · simp [he]
    · have hnd : ¬ d ∣ p := fun h => ((Nat.dvd_prime hp).1 h).elim (by omega) (fun h => he h.symm)
      simp [Nat.dvd_iff_mod_eq_zero] at hnd
      simp [hnd]
  -- A pair (b,v) certifies primorial(b)^16 ≤ 2^v. The preceding endpoint also bounds θ(b).
  let points : List (ℕ × ℕ) := [
    (2,16), (4,42), (6,80), (10,125), (12,181), (16,241), (18,307),
    (22,375), (28,448), (36,605), (42,775), (52,951), (60,1137), (70,1329),
    (78,1527), (88,1730), (100,1940), (108,2262), (126,2480), (138,2818), (156,3164),
    (172,3517), (190,3876), (210,4363), (228,4737), (250,5242), (270,5756), (282,6146),
    (306,6408), (330,6939), (358,7613), (382,8159), (408,8711), (438,9409), (460,9973),
    (486,10541), (508,11114), (546,11693), (586,12571), (616,13457), (646,14201), (672,14800),
    (700,15403), (732,16010), (760,16774), (808,17543), (852,18628), (882,19565), (928,20351),
    (970,21300), (1012,22256), (1048,23217), (1090,24183), (1122,25154), (1162,25804), (1212,26784),
    (1258,27934), (1296,28925), (1320,29754), (1372,30420), (1432,31592), (1482,32937), (1530,34119),
    (1578,35307), (1612,36329), (1656,37183), (1698,38212), (1740,39072), (1786,40108), (1846,41147),
    (1900,42539), (1972,43762), (2028,45517), (2086,46750), (2136,47987), (2206,49228), (2272,50831),
    (2340,52440), (2388,53875), (2436,54954), (2502,56216), (2578,57664), (2662,59481), (2712,61304),
    (2766,62583), (2802,63682), (2850,64600), (2902,65703), (2956,66809), (3018,68102), (3082,69584),
    (3168,71070), (3256,73121), (3330,74991), (3412,76866), (3510,78748), (3582,81012), (3642,82525),
    (3708,84042), (3778,85562), (3850,87085), (3918,88802), (4000,90331), (4072,92247), (4138,93976),
    (4218,95516), (4272,97252), (4348,98605), (4440,100348), (4518,102483), (4602,104234), (4678,106183),
    (4782,107941), (4888,110290), (4972,112646), (5050,114613), (5118,116386), (5208,117965), (5308,120141),
    (5418,122521), (5506,124905), (5622,127095), (5710,129689), (5806,131688), (5868,133891), (5938,135294),
    (6042,136901), (6132,139315), (6228,141532), (6316,143753), (6378,145775), (6468,147192), (6568,149220),
    (6672,151454), (6778,153895), (6868,156341), (6960,158382), (7038,160630), (7126,162267), (7218,164317),
    (7330,166575), (7476,169043), (7582,172546), (7680,174816), (7758,177089), (7872,178952), (7992,181646),
    (8110,184345), (8232,187049), (8362,189965), (8512,192886), (8662,196441), (8778,199792), (8886,202519),
    (9006,205040), (9132,207775), (9240,210724), (9348,213256), (9436,215579), (9520,217693), (9622,219598),
    (9720,221928), (9810,224261), (9886,226384), (9966,228084), (10078,229998), (10168,232553), (10266,234684),
    (10336,236817), (10432,238525), (10528,240662), (10638,243016), (10732,245372), (10852,247516), (10972,250306),
    (11092,253100), (11238,255897), (11382,259344), (11518,262580), (11698,265821), (11866,269933), (12036,273834),
    (12202,277741), (12376,281654), (12516,285572), (12640,288841), (12762,291677), (12906,294516), (13008,297795),
    (13126,300202), (13240,302830), (13366,305461), (13486,308314), (13632,311170), (13756,314468), (13878,317329),
    (14008,320193), (14158,323280), (14340,326592), (14532,330793), (14716,335442), (14866,339653), (15016,342981),
    (15172,346535), (15306,350093), (15426,353209), (15550,355882), (15660,358780), (15766,361457), (15880,363912),
    (15972,366369), (16072,368604), (16186,370841), (16318,373527), (16450,376663), (16602,379578), (16746,383169),
    (16920,386539), (17052,390362), (17206,393513), (17382,397118), (17518,401177), (17668,404336), (17836,407724),
    (17980,411567), (18126,414961), (18252,418358), (18370,421304), (18480,424025), (18592,426521), (18742,429019),
    (18918,432428), (19140,436523), (19386,441761), (19570,447461), (19762,451570), (19972,456140), (20146,460943),
    (20332,464834), (20508,469187), (20718,473315), (20928,478136), (21138,482961), (21340,487791), (21522,492396),
    (21700,496774), (21858,500694), (22030,504386), (22156,508312), (22290,511316), (22446,514322), (22620,518024),
    (22768,521960), (22936,525436), (23062,529378), (23196,532162), (23332,535412), (23530,538432), (23676,543081),
    (23818,546337), (23928,549595), (24042,552156), (24120,554951), (24196,556582), (24316,558447), (24438,561246),
    (24570,564046), (24748,567081), (24922,571053), (25120,575261), (25308,579707), (25522,584156), (25716,589077),
    (25918,593533), (26112,598227), (26296,602689), (26478,606919), (26686,611153), (26860,615860), (27016,619863),
    (27190,623398), (27406,627407), (27652,632599), (27846,638267), (28050,642758), (28278,647252), (28516,652696),
    (28686,658144), (28842,661936), (29022,665730), (29200,669764), (29382,673800), (29568,678076), (29760,682355),
    (30010,686875), (30240,692589), (30492,697831), (30762,703792), (31032,709997), (31252,716207), (31510,721226),
    (31750,727206), (32056,732712), (32326,739900), (32562,746134), (32788,751413), (32998,756695), (33198,761500),
    (33408,766308), (33598,771119), (33766,775451), (33922,779303), (34128,782916), (34312,787737), (34486,791837),
    (34650,795938), (34818,799800), (35022,803664), (35200,808255), (35392,812365), (35568,816718), (35802,820832),
    (36012,826401), (36250,831247), (36492,836580), (36708,842159), (36900,847256), (37060,851627), (37252,855271),
    (37462,859889), (37606,864509), (37798,867915), (37992,872296), (38230,876923), (38458,882283), (38710,887647),
    (38952,893501), (39190,899115), (39396,904488), (39630,909375), (39856,914754), (40092,919891), (40350,925275),
    (40626,931398), (40902,937770), (41178,943900), (41442,950279), (41668,956417), (41910,961821), (42130,967228),
    (42330,972391), (42472,977065), (42642,980264), (42772,984202), (42900,987157), (43018,990113), (43158,992823),
    (43320,996027), (43540,999725), (43758,1004904), (43986,1009839), (44188,1015270), (44388,1019963), (44616,1024411),
    (44818,1029849), (45006,1034300), (45246,1038753), (45490,1044198), (45750,1049894), (46026,1055841), (46306,1062287),
    (46590,1068737), (46860,1075439), (47160,1081648), (47490,1088358), (47778,1096066), (48078,1102783), (48408,1109753),
    (48732,1117226), (49032,1124703), (49330,1131686), (49612,1138673), (49876,1145164), (50118,1151159), (50358,1156656),
    (50598,1162406), (50892,1167909), (51202,1174666), (51478,1181677), (51720,1188190), (51970,1193703), (52222,1199470),
    (52516,1205239), (52806,1212015), (53088,1218795), (53358,1225326), (53632,1231609), (53898,1237895), (54180,1243933),
    (54468,1250477), (54726,1257276), (55008,1263070), (55330,1269623), (55660,1276936), (55930,1284757), (56206,1290815),
    (56488,1297381), (56736,1303697), (56950,1309510), (57148,1314566), (57330,1319118), (57528,1323166), (57726,1327721),
    (57900,1332277), (58072,1336328), (58228,1340380), (58392,1343927), (58566,1347728), (58740,1351784), (58962,1355841),
    (59122,1360913), (59272,1364718), (59416,1368017), (59556,1371316), (59670,1374616), (59778,1377155), (59950,1379695),
    (60106,1383759), (60270,1387316), (60456,1391128), (60658,1395450), (60868,1400027), (61056,1404860), (61330,1409186),
    (61560,1415549), (61780,1420896), (62016,1425990), (62232,1431341), (62500,1436439), (62772,1442558), (63072,1448935),
    (63388,1455825), (63646,1462973), (63852,1469102), (64090,1473700), (64380,1479322), (64692,1485969), (65032,1493131),
    (65370,1501064), (65656,1508744), (65928,1515403), (66238,1521808), (66568,1528729), (66918,1536422), (67218,1544632),
    (67510,1551562), (67782,1558237), (68040,1564401), (68370,1570567), (68710,1578021), (69060,1585993), (69426,1593969),
    (69846,1602464), (70236,1612251), (70618,1621012), (70990,1630035), (71340,1638546), (71670,1646545), (71982,1654289),
    (72268,1661519), (72576,1667977), (72892,1675213), (73188,1682451), (73528,1689175), (73866,1697195), (74200,1704960),
    (74526,1712728), (74842,1720240), (75180,1727496), (75520,1735273), (75792,1743053), (76098,1749279), (76440,1756545),
    (76780,1764334), (77152,1772126), (77490,1780700), (77746,1788498), (78040,1794478), (78340,1801240), (78690,1808265),
    (79062,1816334), (79410,1824927), (79800,1833003), (80152,1841864), (80490,1849946), (80802,1857770), (81076,1865075),
    (81352,1871338), (81646,1877603), (81930,1884392), (82192,1891183), (82468,1897192), (82722,1903464), (83002,1909477),
    (83268,1915753), (83560,1922031), (83868,1928573), (84198,1935902), (84498,1943495), (84808,1950305), (85120,1957379),
    (85450,1964718), (85792,1972321), (86170,1980189), (86476,1988847), (86842,1995934), (87220,2004336), (87582,2013266),
    (87886,2021411), (88260,2028508), (88740,2037185), (89136,2048234), (89532,2057445), (89916,2066659), (90226,2075350),
    (90532,2082463), (90900,2089578), (91248,2098014), (91590,2106189), (91968,2114103), (92356,2122811), (92682,2131786),
    (92956,2139179), (93240,2145518), (93496,2152123), (93810,2157937), (94110,2165338), (94426,2172213), (94726,2179618),
    (95020,2186496), (95266,2193112), (95506,2198935), (95736,2204495), (95956,2209791), (96198,2214823), (96450,2220386),
    (96730,2226215), (96978,2232576), (97240,2238408), (97546,2244507), (97848,2251403), (98212,2258566), (98542,2266793),
    (98892,2274492), (99180,2282724), (99522,2289365), (99822,2297070), (100000,2301322)]
  have check : ((((1,0) :: points).zip points).all valid) = true := by
    -- Each comparison is evaluated separately by the kernel.
    iterate 558
      refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
      · decide +kernel
    rfl
  have last : (points.getLastD (1,0)).1 = 100000 := by decide +kernel
  apply certify_theta mark cover valid (fun a u b v h => of_decide_eq_true h) points (1,0) (by decide) check n hn
  rwa [last]

/-- The prime-counting inequality on the certified range has no remaining hypotheses. -/
theorem verified_initial_range :
    ∀ n : ℕ, 2 ≤ n → n ≤ 100000 → (Nat.primeCounting n : ℝ) < Real.logIntegral n :=
  pi_lt_li_of_theta 100000 fun n hn hN => theta_verified_range n (by omega) hN

lemma lower_from_prime_bounds (h : H1) :
    ∀ n : ℕ, 2 ≤ n → n ≤ 10^19 → (Nat.primeCounting n : ℝ) < Real.logIntegral n := by
  have range (k : ℕ) (hk : k+32 ≤ 10^19) : Chebyshev.theta (k+32 : ℕ) ≤ (k+32 : ℕ) := by
    induction k with
    | zero => exact theta_verified_range 32 (by decide) (by decide)
    | succ k ih =>
      rw [show k+1+32 = (k+32)+1 by omega] at hk ⊢
      by_cases small : k+32+1 ≤ 100000
      · exact theta_verified_range _ (by omega) small
      by_cases hp : (k+32+1).Prime
      · exact h _ hp (by omega) hk
      rw [theta_succ, if_neg hp, add_zero]
      exact (ih (by omega)).trans (by exact_mod_cast Nat.le_succ (k+32))
  apply pi_lt_li_of_theta
  intro n hn hN
  simpa only [Nat.sub_add_cancel hn] using range (n-32) (by omega)

/-- Positivity of a weighted average gives a crossing at a real argument. Rounding
that argument down preserves its prime count and decreases the logarithmic integral. -/
lemma crossover_of_weighted_integral {a b c : ℝ} {w : ℝ → ℝ}
    (ha : 2 ≤ Real.exp a) (hab : a ≤ b) (hcap : b < c)
    (hw : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hpos : 0 < ∫ t in a..b, w t * ((Nat.primeCounting ⌊Real.exp t⌋₊ : ℝ) - Real.logIntegral (Real.exp t))) :
    ∃ n : ℕ, 2 ≤ n ∧ (n : ℝ) < Real.exp c ∧ Real.logIntegral n < (Nat.primeCounting n : ℝ) := by
  have crossing : ∃ t ∈ Icc a b, Real.logIntegral (Real.exp t) < (Nat.primeCounting ⌊Real.exp t⌋₊ : ℝ) := by
    by_contra h
    have hi : 0 ≤ ∫ t in a..b, -(w t * ((Nat.primeCounting ⌊Real.exp t⌋₊ : ℝ) - Real.logIntegral (Real.exp t))) := by
      apply intervalIntegral.integral_nonneg hab
      intro t ht
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hw t ht)
        (sub_nonpos.mpr (le_of_not_gt (fun hx => h ⟨t, ht, hx⟩))))
    rw [intervalIntegral.integral_neg] at hi
    exact (not_lt_of_ge (neg_nonneg.mp hi)) hpos
  obtain ⟨t, ht, hgap⟩ := crossing
  have h2 : (2 : ℝ) ≤ Real.exp t := ha.trans (Real.exp_le_exp.mpr ht.1)
  have hn : 2 ≤ ⌊Real.exp t⌋₊ := Nat.le_floor h2
  have hfloor := Nat.floor_le (Real.exp_pos t).le
  exact ⟨_, hn, hfloor.trans_lt (Real.exp_lt_exp.mpr (ht.2.trans_lt hcap)),
    (li_mono (by exact_mod_cast hn) hfloor).trans_lt hgap⟩

lemma upper_from_gaussian (h : H2) :
    ∃ n : ℕ, 2 ≤ n ∧ (n : ℝ) < Real.exp (72795134/100000) ∧
      Real.logIntegral n < (Nat.primeCounting n : ℝ) := by
  let ω : ℝ := 727951335426 / 1000000000
  let η : ℝ := 47 / 69000000
  let α : ℝ := 161 * 10^13
  let w := fun t : ℝ => Real.sqrt (α / (2 * Real.pi)) * Real.exp (-α * (t-ω)^2 / 2) * t /
    (Real.exp (t / 2) * (1 + 2 / t + (251/25) / t^2))
  apply crossover_of_weighted_integral (a := ω-η) (b := ω+η) (w := w) _ _ _ _ h
  · exact (by linarith [Real.exp_one_gt_d9] : (2:ℝ) ≤ Real.exp 1).trans
      (Real.exp_le_exp.mpr (by norm_num [ω, η]))
  · norm_num [ω, η]
  · norm_num [ω, η]
  · intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num [ω, η] : 0 < ω-η) ht.1
    dsimp only [w]
    positivity

theorem main : H1 → H2 → type_of% @SkewesNumber.skewes_crossover_known_bounds := by
  intro hθ hI
  exact ⟨lower_from_prime_bounds hθ, upper_from_gaussian hI⟩

end OMA.R_SkewesNumber_skewes_crossover_known_bounds_R2
