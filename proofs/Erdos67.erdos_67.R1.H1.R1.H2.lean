import OMAReductions.R_Erdos67_erdos_67_R1_H1_R1
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.ModEq

/-!
# Proof of `Erdos67.erdos_67.R1.H1.R1.H2` (Tao's Entropy Decrement and Bilinear Hoeffding Decoupling)

Following Terence Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point
correlations*, Forum Math. Pi **4** (2016), e8 (`arXiv:1509.05422`), Section 3, we prove `H2`
using:
1. An elementary Chebyshev upper bound on `P_H = {p prime : δ H / 2 ≤ p ≤ δ H}` via the central
   binomial coefficient `Nat.choose m (m / 2) ≤ 2 ^ m`.
2. Discretization of an arbitrary 1-bounded sequence `g : ℕ → ℂ` to a finite grid `Alph` of size
   `O(1 / η ^ 2)` incurring error at most `(η / 2) H / log H`.
3. Finite Shannon entropy, Gibbs' variational inequality, and Hoeffding's MGF lemma over the
   independent modular coordinates `Ω_H = ∀ p : P_H, ZMod p`, bounding the discretized bilinear
   correlation by `2 * sqrt (V_H * D_H)` where `D_H = log |Ω_H| - H(Y_H | X_H)`.
4. An entropy decrement argument along a slowly growing multiplicative ladder `H_{r+1} = k_r * H_r`
   with `k_r ≍ (log H_r) / c`, together with logarithmic shift invariance and CRT equidistribution
   of `Y_H`, yielding a scale `H ∈ [H₀, H₁]` with `D_H ≤ c H / log H`.
-/

open Filter Finset Complex
open scoped Topology Classical BigOperators

namespace Erdos67H2

/- ### Section 1: Elementary Real and Analytic Inequalities -/

private lemma half_exp_add_exp_neg_le (y : ℝ) :
    (Real.exp y + Real.exp (-y)) / 2 ≤ Real.exp (y ^ 2 / 2) := by
  suffices hpos : ∀ x : ℝ, 0 ≤ x → (Real.exp x + Real.exp (-x)) / 2 ≤ Real.exp (x ^ 2 / 2) by
    rcases le_total 0 y with hy | hy
    · exact hpos y hy
    · have h1 := hpos (-y) (neg_nonneg.mpr hy)
      have heq1 : (Real.exp (-y) + Real.exp (- -y)) / 2 = (Real.exp y + Real.exp (-y)) / 2 := by
        rw [neg_neg, add_comm]
      have heq2 : (-y) ^ 2 / 2 = y ^ 2 / 2 := by ring
      rwa [heq1, heq2] at h1
  intro x hx
  let g : ℝ → ℝ := fun t => t * (Real.exp t + Real.exp (-t)) - (Real.exp t - Real.exp (-t))
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (t * (Real.exp t - Real.exp (-t))) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => Real.exp u) (Real.exp t) t := Real.hasDerivAt_exp t
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-t) * (-1)) t :=
      (hasDerivAt_neg t).exp
    have hadd : HasDerivAt (fun u : ℝ => Real.exp u + Real.exp (-u))
        (Real.exp t + Real.exp (-t) * (-1)) t := h1.add h2
    have hsub : HasDerivAt (fun u : ℝ => Real.exp u - Real.exp (-u))
        (Real.exp t - Real.exp (-t) * (-1)) t := h1.sub h2
    have hmul : HasDerivAt (fun u : ℝ => u * (Real.exp u + Real.exp (-u)))
        (1 * (Real.exp t + Real.exp (-t)) + t * (Real.exp t + Real.exp (-t) * (-1))) t :=
      (hasDerivAt_id t).mul hadd
    have htot := hmul.sub hsub
    have heq : (1 * (Real.exp t + Real.exp (-t)) + t * (Real.exp t + Real.exp (-t) * (-1))) -
        (Real.exp t - Real.exp (-t) * (-1)) = t * (Real.exp t - Real.exp (-t)) := by ring
    rw [heq] at htot
    exact htot
  have hg_mono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ => (hg_deriv t).continuousAt.continuousWithinAt)
      (fun t _ => (hg_deriv t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    have ht_pos : 0 < t := Set.mem_Ioi.mp ht
    rw [(hg_deriv t).deriv]
    have hle : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
    exact mul_nonneg ht_pos.le (sub_nonneg.mpr hle)
  have hg_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ g t := by
    intro t ht
    have h0 : g 0 = 0 := by simp [g]
    rw [← h0]
    exact hg_mono Set.self_mem_Ici ht ht
  let h : ℝ → ℝ := fun t => Real.exp (-(t ^ 2 / 2)) * ((Real.exp t + Real.exp (-t)) / 2)
  have hh_deriv : ∀ t : ℝ, HasDerivAt h (-(Real.exp (-(t ^ 2 / 2)) * g t / 2)) t := by
    intro t
    have hsq : HasDerivAt (fun u : ℝ => -(u ^ 2 / 2)) (-t) t := by
      have hpow : HasDerivAt (fun u : ℝ => u ^ 2) ((2 : ℕ) * t ^ (2 - 1)) t := hasDerivAt_pow 2 t
      have h1 := (hpow.div_const 2).neg
      have heq : -(((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2) = -t := by norm_num
      rw [heq] at h1
      exact h1
    have hexp1 : HasDerivAt (fun u : ℝ => Real.exp (-(u ^ 2 / 2)))
        (Real.exp (-(t ^ 2 / 2)) * (-t)) t := hsq.exp
    have h1 : HasDerivAt (fun u : ℝ => Real.exp u) (Real.exp t) t := Real.hasDerivAt_exp t
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-t) * (-1)) t :=
      (hasDerivAt_neg t).exp
    have havg : HasDerivAt (fun u : ℝ => (Real.exp u + Real.exp (-u)) / 2)
        ((Real.exp t + Real.exp (-t) * (-1)) / 2) t := (h1.add h2).div_const 2
    have htot := hexp1.mul havg
    have heq : Real.exp (-(t ^ 2 / 2)) * (-t) * ((Real.exp t + Real.exp (-t)) / 2) +
        Real.exp (-(t ^ 2 / 2)) * ((Real.exp t + Real.exp (-t) * (-1)) / 2) =
        -(Real.exp (-(t ^ 2 / 2)) * g t / 2) := by
      dsimp [g]; ring
    rw [heq] at htot
    exact htot
  have hh_anti : AntitoneOn h (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hh_deriv t).continuousAt.continuousWithinAt)
      (fun t _ => (hh_deriv t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    have ht_pos : 0 < t := Set.mem_Ioi.mp ht
    rw [(hh_deriv t).deriv]
    have hgn := hg_nonneg t ht_pos.le
    have hexp_pos : 0 < Real.exp (-(t ^ 2 / 2)) := Real.exp_pos _
    linarith [mul_nonneg hexp_pos.le hgn]
  have hh_le : h x ≤ h 0 := hh_anti Set.self_mem_Ici hx hx
  have hh0 : h 0 = 1 := by simp [h]
  rw [hh0] at hh_le
  dsimp [h] at hh_le
  have hmul := mul_le_mul_of_nonneg_left hh_le (Real.exp_pos (x ^ 2 / 2)).le
  rw [mul_one, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hmul
  exact hmul

private lemma hoeffding_mgf {α : Type*} [Fintype α] [Nonempty α]
    (w : α → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hmean : ∑ a : α, w a = 0) (hbd : ∀ a : α, |w a| ≤ b) (t : ℝ) :
    (1 / (Fintype.card α : ℝ)) * ∑ a : α, Real.exp (t * w a) ≤ Real.exp (t ^ 2 * b ^ 2 / 2) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  rcases eq_or_lt_of_le hb with rfl | hb_pos
  · have hw0 : ∀ a : α, w a = 0 := fun a => by
      have := hbd a
      exact abs_nonpos_iff.mp this
    simp [hw0, hcard_pos.ne']
  · have hpt : ∀ a : α,
        Real.exp (t * w a) ≤
          ((b - w a) / (2 * b)) * Real.exp (-(t * b)) +
          ((b + w a) / (2 * b)) * Real.exp (t * b) := by
      intro a
      have hwa := abs_le.mp (hbd a)
      have hc1 : 0 ≤ (b - w a) / (2 * b) := div_nonneg (by linarith) (by positivity)
      have hc2 : 0 ≤ (b + w a) / (2 * b) := div_nonneg (by linarith) (by positivity)
      have hcsum : (b - w a) / (2 * b) + (b + w a) / (2 * b) = 1 := by
        field_simp [hb_pos.ne']; ring
      have hcomb : ((b - w a) / (2 * b)) * (-(t * b)) + ((b + w a) / (2 * b)) * (t * b) = t * w a := by
        field_simp [hb_pos.ne']; ring
      have hconv := convexOn_exp.2 (Set.mem_univ (-(t * b))) (Set.mem_univ (t * b)) hc1 hc2 hcsum
      simpa only [smul_eq_mul, hcomb] using hconv
    have hsum : ∑ a : α, Real.exp (t * w a) ≤
        (Fintype.card α : ℝ) * ((Real.exp (t * b) + Real.exp (-(t * b))) / 2) := by
      calc ∑ a : α, Real.exp (t * w a)
          ≤ ∑ a : α, (((b - w a) / (2 * b)) * Real.exp (-(t * b)) +
              ((b + w a) / (2 * b)) * Real.exp (t * b)) :=
            Finset.sum_le_sum fun a _ => hpt a
        _ = (∑ a : α, ((b - w a) / (2 * b))) * Real.exp (-(t * b)) +
            (∑ a : α, ((b + w a) / (2 * b))) * Real.exp (t * b) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        _ = ((Fintype.card α : ℝ) / 2) * Real.exp (-(t * b)) +
            ((Fintype.card α : ℝ) / 2) * Real.exp (t * b) := by
            have hs1 : ∑ a : α, (b - w a) / (2 * b) = (Fintype.card α : ℝ) / 2 := by
              rw [← Finset.sum_div, Finset.sum_sub_distrib, hmean, sub_zero,
                Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              field_simp [hb_pos.ne']
            have hs2 : ∑ a : α, (b + w a) / (2 * b) = (Fintype.card α : ℝ) / 2 := by
              rw [← Finset.sum_div, Finset.sum_add_distrib, hmean, add_zero,
                Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              field_simp [hb_pos.ne']
            rw [hs1, hs2]
        _ = (Fintype.card α : ℝ) * ((Real.exp (t * b) + Real.exp (-(t * b))) / 2) := by ring
    calc (1 / (Fintype.card α : ℝ)) * ∑ a : α, Real.exp (t * w a)
        ≤ (1 / (Fintype.card α : ℝ)) *
            ((Fintype.card α : ℝ) * ((Real.exp (t * b) + Real.exp (-(t * b))) / 2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (Real.exp (t * b) + Real.exp (-(t * b))) / 2 := by field_simp [hcard_pos.ne']
      _ ≤ Real.exp ((t * b) ^ 2 / 2) := half_exp_add_exp_neg_le (t * b)
      _ = Real.exp (t ^ 2 * b ^ 2 / 2) := by congr 1; ring

private lemma neg_mul_log_le_two_sqrt {u : ℝ} (hu0 : 0 ≤ u) :
    -u * Real.log u ≤ 2 * Real.sqrt u := by
  rcases eq_or_lt_of_le hu0 with rfl | hu_pos
  · simp
  · have hsq_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu_pos
    have hlog := Real.log_le_sub_one_of_pos (one_div_pos.mpr hsq_pos)
    have hlog_eq : Real.log (1 / Real.sqrt u) = -(1 / 2) * Real.log u := by
      rw [one_div, Real.log_inv, Real.log_sqrt hu0]; ring
    rw [hlog_eq] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 2 * u)
    have h1 : 2 * u * (-(1 / 2) * Real.log u) = -u * Real.log u := by ring
    have h2 : 2 * u * (1 / Real.sqrt u - 1) = 2 * Real.sqrt u - 2 * u := by
      have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0
      field_simp [hsq_pos.ne']
      nlinarith
    linarith

private lemma neg_mul_log_holder {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |(-x * Real.log x) - (-y * Real.log y)| ≤ 2 * Real.sqrt |x - y| := by
  suffices hord : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      |(-a * Real.log a) - (-b * Real.log b)| ≤ 2 * Real.sqrt (b - a) by
    rcases le_total x y with hxy | hyx
    · rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact hord x y hx0 hxy hy1
    · rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_sub_comm (-x * Real.log x)]
      exact hord y x hy0 hyx hx1
  intro a b ha0 hab hb1
  set d : ℝ := b - a
  have hd0 : 0 ≤ d := sub_nonneg.mpr hab
  have hd1 : d ≤ 1 := by linarith
  have hupper : (-b * Real.log b) - (-a * Real.log a) ≤ 2 * Real.sqrt d := by
    have hstep : (-b * Real.log b) - (-a * Real.log a) ≤ -d * Real.log d := by
      rcases eq_or_lt_of_le ha0 with rfl | ha_pos
      · simp [d]
      rcases eq_or_lt_of_le hd0 with hd_eq | hd_pos
      · have : a = b := by linarith
        subst this; simp [d]
      · have hb_pos : 0 < b := by linarith
        have h1 : a * Real.log (a / b) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos ha0 (Real.log_nonpos (by positivity) ((div_le_one hb_pos).mpr hab))
        have h2 : d * Real.log (d / b) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hd0 (Real.log_nonpos (by positivity) ((div_le_one hb_pos).mpr (by linarith)))
        rw [Real.log_div ha_pos.ne' hb_pos.ne'] at h1
        rw [Real.log_div hd_pos.ne' hb_pos.ne'] at h2
        have hb_eq : b = a + d := by dsimp [d]; ring
        linarith
    exact hstep.trans (neg_mul_log_le_two_sqrt hd0)
  have hlower : (-a * Real.log a) - (-b * Real.log b) ≤ 2 * Real.sqrt d := by
    let f : ℝ → ℝ := fun t => t * (1 - Real.log t)
    have hf_cont : ContinuousOn f (Set.Icc 0 1) := by
      have h1 : Continuous (fun t : ℝ => t - t * Real.log t) :=
        continuous_id.sub Real.continuous_mul_log
      have hfeq : f = fun t => t - t * Real.log t := funext fun t => by dsimp [f]; ring
      rw [hfeq]; exact h1.continuousOn
    have hf_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (-Real.log t) t := by
      intro t ht
      have ht0 : t ≠ 0 := ht.1.ne'
      have h1 : HasDerivAt (fun u : ℝ => 1 - Real.log u) (0 - t⁻¹) t :=
        (hasDerivAt_const t (1 : ℝ)).sub (Real.hasDerivAt_log ht0)
      have hmul := (hasDerivAt_id t).mul h1
      dsimp only [id_eq] at hmul
      have heq : 1 * (1 - Real.log t) + t * (0 - t⁻¹) = -Real.log t := by
        rw [one_mul, zero_sub, mul_neg, mul_inv_cancel₀ ht0]; ring
      rw [heq] at hmul
      exact hmul
    have hf_mono : MonotoneOn f (Set.Icc 0 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hf_cont
        (fun t ht => by
          rw [interior_Icc] at ht
          exact (hf_deriv t ht).differentiableAt.differentiableWithinAt) ?_
      intro t ht
      rw [interior_Icc] at ht
      rw [(hf_deriv t ht).deriv]
      have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.1.le ht.2.le
      linarith
    have hfa_le_fb : f a ≤ f b := hf_mono ⟨ha0, hab.trans hb1⟩ ⟨ha0.trans hab, hb1⟩ hab
    have hd_le_sqrt : d ≤ Real.sqrt d := by
      rw [Real.le_sqrt hd0 hd0]; nlinarith
    dsimp [f] at hfa_le_fb
    have hsq_nn : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
    linarith
  rw [abs_le]
  constructor <;> linarith

/- ### Section 2: Elementary Chebyshev Bounds on `P_H` -/

private noncomputable def primeWindow (δ : ℝ) (H : ℕ) : Finset ℕ :=
  (Finset.Icc (Nat.ceil (δ * (H : ℝ) / 2)) (Nat.floor (δ * (H : ℝ)))).filter Nat.Prime

private lemma choose_le_two_pow (m k : ℕ) : Nat.choose m k ≤ 2 ^ m := by
  by_cases hkm : k ≤ m
  · calc Nat.choose m k
        ≤ ∑ i ∈ Finset.range (m + 1), Nat.choose m i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      _ = 2 ^ m := Nat.sum_range_choose m
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; exact Nat.zero_le _

private lemma prod_primes_dvd_central_choose (m : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ m - m / 2 < p ∧ p ≤ m) :
    (∏ p ∈ S, p) ∣ Nat.choose m (m / 2) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
    rw [Finset.prod_insert hpS]
    have hp := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime ∧ m - m / 2 < q ∧ q ≤ m :=
      fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hp_dvd : p ∣ Nat.choose m (m / 2) := by
      obtain ⟨hpr, hgt, hle⟩ := hp
      have hfac := Nat.choose_mul_factorial_mul_factorial (Nat.div_le_self m 2)
      have hdvd_m : p ∣ m.factorial := hpr.dvd_factorial.mpr hle
      have hndvd1 : ¬ p ∣ (m / 2).factorial := by rw [hpr.dvd_factorial]; omega
      have hndvd2 : ¬ p ∣ (m - m / 2).factorial := by rw [hpr.dvd_factorial]; omega
      rw [← hfac] at hdvd_m
      rcases hpr.dvd_mul.mp hdvd_m with h1 | h2
      · rcases hpr.dvd_mul.mp h1 with h3 | h4
        · exact h3
        · exact absurd h4 hndvd1
      · exact absurd h2 hndvd2
    have hcop : Nat.Coprime p (∏ q ∈ S, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hne : p ≠ q := fun heq => hpS (heq ▸ hq)
      exact (Nat.coprime_primes hp.1 (hS' q hq).1).mpr hne
    exact hcop.mul_dvd_of_dvd_of_dvd hp_dvd (ih hS')

private lemma chebyshev_P_H_bounds {δ : ℝ} {H : ℕ}
    (hδ0 : 0 < δ) (hδ14 : δ ≤ 1 / 4) (hH : (16 / δ ^ 2 + 100 : ℝ) ≤ (H : ℝ)) :
    1 ≤ Real.log (H : ℝ) ∧
    Real.log ((∏ p ∈ primeWindow δ H, p : ℕ) : ℝ) ≤ (H : ℝ) ∧
    ∑ p ∈ primeWindow δ H, (1 : ℝ) / (p : ℝ) ≤ 6 / Real.log (H : ℝ) ∧
    ∑ p ∈ primeWindow δ H, (1 : ℝ) / ((p : ℝ) ^ 2) ≤ 12 / (δ * (H : ℝ) * Real.log (H : ℝ)) := by
  have hH100 : (100 : ℝ) ≤ (H : ℝ) := by
    have : 0 < 16 / δ ^ 2 := by positivity
    linarith
  have hH_pos : (0 : ℝ) < (H : ℝ) := by linarith
  have hlogH_ge1 : 1 ≤ Real.log (H : ℝ) := by
    have h1 : Real.exp 1 ≤ (H : ℝ) := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  have hlogH_pos : 0 < Real.log (H : ℝ) := by linarith
  have hδH_ge4sq : 4 * Real.sqrt (H : ℝ) ≤ δ * (H : ℝ) := by
    have h16 : 16 / δ ^ 2 ≤ (H : ℝ) := by linarith
    have hsq : 16 ≤ δ ^ 2 * (H : ℝ) := by
      have := (div_le_iff₀ (by positivity : 0 < δ ^ 2)).mp h16
      linarith
    have h4 : (4 : ℝ) ≤ δ * Real.sqrt (H : ℝ) := by
      have hsq' : (4 : ℝ) ^ 2 ≤ (δ * Real.sqrt (H : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hH_pos.le]; linarith
      nlinarith [mul_nonneg hδ0.le (Real.sqrt_nonneg (H : ℝ))]
    calc 4 * Real.sqrt (H : ℝ) ≤ (δ * Real.sqrt (H : ℝ)) * Real.sqrt (H : ℝ) :=
          mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg _)
      _ = δ * (Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ)) := by ring
      _ = δ * (H : ℝ) := by rw [Real.mul_self_sqrt hH_pos.le]
  have hsqH_ge10 : 10 ≤ Real.sqrt (H : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hH_pos.le]; linarith
  have hδH_ge40 : 40 ≤ δ * (H : ℝ) := by linarith
  set m : ℕ := Nat.floor (δ * (H : ℝ))
  have hm_le : (m : ℝ) ≤ δ * (H : ℝ) := Nat.floor_le (by positivity)
  have hm_gt : δ * (H : ℝ) - 1 < (m : ℝ) := by
    have := Nat.lt_floor_add_one (δ * (H : ℝ)); linarith
  have hm_ge39 : 39 ≤ m := by
    have : (39 : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast this
  let P := primeWindow δ H
  let P_hi : Finset ℕ := P.filter (fun p => m - m / 2 < p)
  let P_lo : Finset ℕ := P.filter (fun p => ¬ (m - m / 2 < p))
  have hP_union : P = P_hi ∪ P_lo := by
    ext p; simp only [P_hi, P_lo, Finset.mem_union, Finset.mem_filter]; tauto
  have hP_disj : Disjoint P_hi P_lo := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
  have hP_mem_bounds : ∀ p ∈ P, p.Prime ∧ δ * (H : ℝ) / 2 ≤ (p : ℝ) ∧ p ≤ m := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpI := Finset.mem_Icc.mp hp'.1
    exact ⟨hp'.2, (Nat.le_ceil (δ * (H : ℝ) / 2)).trans (by exact_mod_cast hpI.1), hpI.2⟩
  have hPlo_sub : P_lo ⊆ Finset.Icc (m / 2) (m - m / 2) := by
    intro p hp
    have hp1 := (Finset.mem_filter.mp hp).1
    have hp2 := (Finset.mem_filter.mp hp).2
    have hbd := (hP_mem_bounds p hp1).2.1
    have hge : (m / 2 : ℕ) ≤ p := by
      have h1 : ((m / 2 : ℕ) : ℝ) ≤ δ * (H : ℝ) / 2 := by
        have : (m / 2 : ℕ) * 2 ≤ m := Nat.div_mul_le_self m 2
        have h2 : ((m / 2 : ℕ) : ℝ) * 2 ≤ (m : ℝ) := by exact_mod_cast this
        linarith
      exact_mod_cast h1.trans hbd
    exact Finset.mem_Icc.mpr ⟨hge, by omega⟩
  have hPlo_card : P_lo.card ≤ 2 := by
    calc P_lo.card ≤ (Finset.Icc (m / 2) (m - m / 2)).card := Finset.card_le_card hPlo_sub
      _ = (m - m / 2) + 1 - m / 2 := Nat.card_Icc _ _
      _ ≤ 2 := by omega
  have hPhi_prod_le : ∏ p ∈ P_hi, p ≤ 2 ^ m := by
    have hdvd : (∏ p ∈ P_hi, p) ∣ Nat.choose m (m / 2) :=
      prod_primes_dvd_central_choose m P_hi fun p hp => by
        have hp1 := Finset.mem_filter.mp hp
        have hb := hP_mem_bounds p hp1.1
        exact ⟨hb.1, hp1.2, hb.2.2⟩
    have hpos : 0 < Nat.choose m (m / 2) := Nat.choose_pos (Nat.div_le_self m 2)
    exact (Nat.le_of_dvd hpos hdvd).trans (choose_le_two_pow m (m / 2))
  have hPlo_prod_le : ∏ p ∈ P_lo, p ≤ m ^ 2 := by
    calc ∏ p ∈ P_lo, p ≤ ∏ _p ∈ P_lo, m :=
          Finset.prod_le_prod' fun p hp => (hP_mem_bounds p (Finset.mem_filter.mp hp).1).2.2
      _ = m ^ P_lo.card := by simp
      _ ≤ m ^ 2 := Nat.pow_le_pow_right (by omega) hPlo_card
  have hP_prod_le : ∏ p ∈ P, p ≤ 2 ^ m * m ^ 2 := by
    rw [hP_union, Finset.prod_union hP_disj]
    exact Nat.mul_le_mul hPhi_prod_le hPlo_prod_le
  have hprod_pos : 0 < ∏ p ∈ P, p :=
    Finset.prod_pos fun p hp => (hP_mem_bounds p hp).1.pos
  have hlog_prod : Real.log ((∏ p ∈ P, p : ℕ) : ℝ) ≤ (H : ℝ) := by
    have hleR : ((∏ p ∈ P, p : ℕ) : ℝ) ≤ (2 : ℝ) ^ m * (m : ℝ) ^ 2 := by
      exact_mod_cast hP_prod_le
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hlogm : 2 * Real.log (m : ℝ) ≤ (m : ℝ) := by
      have hexp : (m : ℝ) ≤ Real.exp ((m : ℝ) / 2) := by
        have hq : 1 + (m : ℝ) / 2 + ((m : ℝ) / 2) ^ 2 / 2 ≤ Real.exp ((m : ℝ) / 2) := by
          have := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ (m : ℝ) / 2) 3
          simp [Finset.sum_range_succ, Nat.factorial] at this
          linarith
        have hm39 : (39 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge39
        nlinarith
      have h1 := Real.log_le_log hm_pos hexp
      rw [Real.log_exp] at h1
      linarith
    calc Real.log ((∏ p ∈ P, p : ℕ) : ℝ)
        ≤ Real.log ((2 : ℝ) ^ m * (m : ℝ) ^ 2) :=
          Real.log_le_log (by exact_mod_cast hprod_pos) hleR
      _ = (m : ℝ) * Real.log 2 + 2 * Real.log (m : ℝ) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
          push_cast; ring
      _ ≤ (m : ℝ) * 1 + (m : ℝ) := by gcongr
      _ = 2 * (m : ℝ) := by ring
      _ ≤ 2 * (δ * (H : ℝ)) := by linarith
      _ ≤ (H : ℝ) := by nlinarith
  have hPhi_card : (P_hi.card : ℝ) ≤ 2 * δ * (H : ℝ) / Real.log (H : ℝ) := by
    have hpow : (δ * (H : ℝ) / 2) ^ P_hi.card ≤ (2 : ℝ) ^ m := by
      calc (δ * (H : ℝ) / 2) ^ P_hi.card
          = ∏ _p ∈ P_hi, (δ * (H : ℝ) / 2) := (Finset.prod_const _).symm
        _ ≤ ∏ p ∈ P_hi, (p : ℝ) :=
            Finset.prod_le_prod (fun _ _ => by positivity) fun p hp =>
              (hP_mem_bounds p (Finset.mem_filter.mp hp).1).2.1
        _ = ((∏ p ∈ P_hi, p : ℕ) : ℝ) := by rw [Nat.cast_prod]
        _ ≤ (2 : ℝ) ^ m := by exact_mod_cast hPhi_prod_le
    have hlog_pow := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlog_pow
    have hlog_half : (1 / 2) * Real.log (H : ℝ) ≤ Real.log (δ * (H : ℝ) / 2) := by
      have hsq_le : Real.sqrt (H : ℝ) ≤ δ * (H : ℝ) / 2 := by linarith
      have := Real.log_le_log (Real.sqrt_pos.mpr hH_pos) hsq_le
      rw [Real.log_sqrt hH_pos.le] at this
      linarith
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hstep : (P_hi.card : ℝ) * ((1 / 2) * Real.log (H : ℝ)) ≤ δ * (H : ℝ) := by
      calc (P_hi.card : ℝ) * ((1 / 2) * Real.log (H : ℝ))
          ≤ (P_hi.card : ℝ) * Real.log (δ * (H : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hlog_half (Nat.cast_nonneg _)
        _ ≤ (m : ℝ) * Real.log 2 := hlog_pow
        _ ≤ (m : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
        _ ≤ δ * (H : ℝ) := by linarith
    rw [le_div_iff₀ hlogH_pos]
    linarith
  have hP_card : (P.card : ℝ) ≤ 3 * δ * (H : ℝ) / Real.log (H : ℝ) := by
    have hcard_eq : P.card = P_hi.card + P_lo.card := by
      rw [hP_union, Finset.card_union_of_disjoint hP_disj]
    have h2_le : (2 : ℝ) ≤ δ * (H : ℝ) / Real.log (H : ℝ) := by
      rw [le_div_iff₀ hlogH_pos]
      have hlog_sq : Real.log (H : ℝ) ≤ 2 * Real.sqrt (H : ℝ) := by
        have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hH_pos)
        rw [Real.log_sqrt hH_pos.le] at this
        linarith
      linarith
    have hPlo_r : (P_lo.card : ℝ) ≤ 2 := by exact_mod_cast hPlo_card
    have hcard_r : (P.card : ℝ) = (P_hi.card : ℝ) + (P_lo.card : ℝ) := by exact_mod_cast hcard_eq
    have hsum3 : 2 * δ * (H : ℝ) / Real.log (H : ℝ) + δ * (H : ℝ) / Real.log (H : ℝ) =
        3 * δ * (H : ℝ) / Real.log (H : ℝ) := by ring
    linarith
  have hrec1 : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ≤ 6 / Real.log (H : ℝ) := by
    have hdh_pos : 0 < δ * (H : ℝ) / 2 := by positivity
    calc ∑ p ∈ P, (1 : ℝ) / (p : ℝ)
        ≤ ∑ _p ∈ P, (1 : ℝ) / (δ * (H : ℝ) / 2) :=
          Finset.sum_le_sum fun p hp => one_div_le_one_div_of_le hdh_pos (hP_mem_bounds p hp).2.1
      _ = (P.card : ℝ) / (δ * (H : ℝ) / 2) := by simp [div_eq_mul_inv]
      _ ≤ (3 * δ * (H : ℝ) / Real.log (H : ℝ)) / (δ * (H : ℝ) / 2) :=
          div_le_div_of_nonneg_right hP_card hdh_pos.le
      _ = 6 / Real.log (H : ℝ) := by field_simp [hδ0.ne', hH_pos.ne', hlogH_pos.ne']; ring
  have hrec2 : ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) ^ 2) ≤ 12 / (δ * (H : ℝ) * Real.log (H : ℝ)) := by
    have hdh_pos : 0 < δ * (H : ℝ) / 2 := by positivity
    calc ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) ^ 2)
        ≤ ∑ p ∈ P, (1 / (δ * (H : ℝ) / 2)) * (1 / (p : ℝ)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hP_mem_bounds p hp).1.pos
          have h1 := one_div_le_one_div_of_le hdh_pos (hP_mem_bounds p hp).2.1
          calc (1 : ℝ) / ((p : ℝ) ^ 2) = (1 / (p : ℝ)) * (1 / (p : ℝ)) := by ring
            _ ≤ (1 / (δ * (H : ℝ) / 2)) * (1 / (p : ℝ)) := by gcongr
      _ = (1 / (δ * (H : ℝ) / 2)) * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ (1 / (δ * (H : ℝ) / 2)) * (6 / Real.log (H : ℝ)) := by gcongr
      _ = 12 / (δ * (H : ℝ) * Real.log (H : ℝ)) := by
          field_simp [hδ0.ne', hH_pos.ne', hlogH_pos.ne']; ring
  exact ⟨hlogH_ge1, hlog_prod, hrec1, hrec2⟩

/- ### Section 3: Finite Shannon Entropy, Gibbs Inequality, and Subadditivity -/

private noncomputable def shannonH {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  - ∑ a : α, p a * Real.log (p a)

private noncomputable def dist {ι α : Type*} (I : Finset ι) (μ : ι → ℝ) (U : ι → α) (a : α) : ℝ :=
  ∑ n ∈ I, if U n = a then μ n else 0

private lemma dist_nonneg {ι α : Type*} (I : Finset ι) (μ : ι → ℝ)
    (hμ : ∀ n ∈ I, 0 ≤ μ n) (U : ι → α) (a : α) : 0 ≤ dist I μ U a := by
  refine Finset.sum_nonneg fun n hn => ?_
  split_ifs
  · exact hμ n hn
  · exact le_rfl

private lemma sum_dist_eq_one {ι α : Type*} [Fintype α] (I : Finset ι) (μ : ι → ℝ)
    (hμ1 : ∑ n ∈ I, μ n = 1) (U : ι → α) : ∑ a : α, dist I μ U a = 1 := by
  dsimp [dist]
  rw [Finset.sum_comm]
  trans ∑ n ∈ I, μ n
  · refine Finset.sum_congr rfl fun n _ => ?_
    simp
  · exact hμ1

private lemma dist_le_one {ι α : Type*} [Fintype α] (I : Finset ι) (μ : ι → ℝ)
    (hμ0 : ∀ n ∈ I, 0 ≤ μ n) (hμ1 : ∑ n ∈ I, μ n = 1) (U : ι → α) (a : α) :
    dist I μ U a ≤ 1 := by
  rw [← sum_dist_eq_one I μ hμ1 U]
  exact Finset.single_le_sum (fun b _ => dist_nonneg I μ hμ0 U b) (Finset.mem_univ a)

private lemma shannonH_nonneg {α : Type*} [Fintype α] (p : α → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1) : 0 ≤ shannonH p := by
  dsimp [shannonH]
  rw [neg_nonneg]
  refine Finset.sum_nonpos fun a _ => ?_
  exact mul_nonpos_of_nonneg_of_nonpos (hp0 a) (Real.log_nonpos (hp0 a) (hp1 a))

private lemma gibbs_ineq {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → ℝ) (hP0 : ∀ y, 0 ≤ P y) (hP1 : ∑ y : Ω, P y = 1) (ψ : Ω → ℝ) :
    ∑ y : Ω, P y * ψ y ≤
      (Real.log (Fintype.card Ω : ℝ) - shannonH P) +
      Real.log ((1 / (Fintype.card Ω : ℝ)) * ∑ y : Ω, Real.exp (ψ y)) := by
  set Z : ℝ := ∑ y : Ω, Real.exp (ψ y)
  have hZ_pos : 0 < Z :=
    Finset.sum_pos (fun y _ => Real.exp_pos (ψ y)) Finset.univ_nonempty
  have hcard_pos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpt : ∀ y : Ω, P y * ψ y - P y * Real.log Z - P y * Real.log (P y) ≤ Real.exp (ψ y) / Z - P y := by
    intro y
    rcases eq_or_lt_of_le (hP0 y) with hy0 | hy_pos
    · rw [← hy0]; simp; positivity
    · have hq_pos : 0 < Real.exp (ψ y) / Z := div_pos (Real.exp_pos _) hZ_pos
      have hlog := Real.log_le_sub_one_of_pos (div_pos hq_pos hy_pos)
      rw [Real.log_div hq_pos.ne' hy_pos.ne', Real.log_div (Real.exp_pos _).ne' hZ_pos.ne',
        Real.log_exp] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hy_pos.le
      have hrhs : P y * (Real.exp (ψ y) / Z / P y - 1) = Real.exp (ψ y) / Z - P y := by
        field_simp [hy_pos.ne']
      linarith
  have hsum := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hpt y
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hP1, one_mul,
    Finset.sum_sub_distrib, ← Finset.sum_div, hP1, div_self hZ_pos.ne', sub_self] at hsum
  have hlogZ : Real.log Z = Real.log (Fintype.card Ω : ℝ) +
      Real.log ((1 / (Fintype.card Ω : ℝ)) * Z) := by
    rw [← Real.log_mul hcard_pos.ne' (by positivity)]
    congr 1; field_simp [hcard_pos.ne']
  dsimp [shannonH]
  linarith

private lemma shannonH_le_log_card {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → ℝ) (hP0 : ∀ y, 0 ≤ P y) (hP1 : ∑ y : Ω, P y = 1) :
    shannonH P ≤ Real.log (Fintype.card Ω : ℝ) := by
  have h := gibbs_ineq P hP0 hP1 (fun _ => 0)
  have hcard_pos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hone : (1 / (Fintype.card Ω : ℝ)) * ∑ _y : Ω, Real.exp 0 = 1 := by
    simp [hcard_pos.ne']
  rw [hone, Real.log_one, add_zero] at h
  simp only [mul_zero, Finset.sum_const_zero] at h
  linarith

private lemma shannonH_equiv {ι α β : Type*} [Fintype α] [Fintype β]
    (I : Finset ι) (μ : ι → ℝ) (U : ι → α) (e : α ≃ β) :
    shannonH (dist I μ (e ∘ U)) = shannonH (dist I μ U) := by
  dsimp [shannonH]
  congr 1
  refine Fintype.sum_equiv e.symm _ _ fun b => ?_
  have hdist : dist I μ (e ∘ U) b = dist I μ U (e.symm b) := by
    dsimp [dist]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [← Equiv.eq_symm_apply]
  rw [hdist]

private lemma shannonH_subadd_dist {α β : Type*} [Fintype α] [Fintype β]
    (P : α × β → ℝ) (hP0 : ∀ ab, 0 ≤ P ab) (hP1 : ∑ ab : α × β, P ab = 1) :
    shannonH P ≤ shannonH (fun a => ∑ b : β, P (a, b)) + shannonH (fun b => ∑ a : α, P (a, b)) := by
  let P1 : α → ℝ := fun a => ∑ b : β, P (a, b)
  let P2 : β → ℝ := fun b => ∑ a : α, P (a, b)
  have hP1_nn : ∀ a, 0 ≤ P1 a := fun a => Finset.sum_nonneg fun b _ => hP0 (a, b)
  have hP2_nn : ∀ b, 0 ≤ P2 b := fun b => Finset.sum_nonneg fun a _ => hP0 (a, b)
  have hpt : ∀ ab : α × β,
      P ab * Real.log (P1 ab.1) + P ab * Real.log (P2 ab.2) - P ab * Real.log (P ab) ≤
        P1 ab.1 * P2 ab.2 - P ab := by
    intro ⟨a, b⟩
    rcases eq_or_lt_of_le (hP0 (a, b)) with h0 | hpos
    · rw [← h0]; simp; exact mul_nonneg (hP1_nn a) (hP2_nn b)
    · have h1_pos : 0 < P1 a := lt_of_lt_of_le hpos
        (Finset.single_le_sum (fun b' _ => hP0 (a, b')) (Finset.mem_univ b))
      have h2_pos : 0 < P2 b := lt_of_lt_of_le hpos
        (Finset.single_le_sum (fun a' _ => hP0 (a', b)) (Finset.mem_univ a))
      have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos h1_pos h2_pos) hpos)
      rw [Real.log_div (mul_pos h1_pos h2_pos).ne' hpos.ne', Real.log_mul h1_pos.ne' h2_pos.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
      have hrhs : P (a, b) * (P1 a * P2 b / P (a, b) - 1) = P1 a * P2 b - P (a, b) := by
        field_simp [hpos.ne']
      linarith
  have hsum := Finset.sum_le_sum fun ab (_ : ab ∈ Finset.univ) => hpt ab
  have hprod_sum : ∑ ab : α × β, P1 ab.1 * P2 ab.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    have hs1 : ∑ a : α, P1 a = 1 := by rw [← Fintype.sum_prod_type]; exact hP1
    have hs2 : ∑ b : β, P2 b = 1 := by
      dsimp [P2]; rw [Finset.sum_comm, ← Fintype.sum_prod_type]; exact hP1
    rw [hs1, hs2, one_mul]
  have hmarg1 : ∑ ab : α × β, P ab * Real.log (P1 ab.1) = ∑ a : α, P1 a * Real.log (P1 a) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only
    rw [← Finset.sum_mul]
  have hmarg2 : ∑ ab : α × β, P ab * Real.log (P2 ab.2) = ∑ b : β, P2 b * Real.log (P2 b) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    dsimp only
    rw [← Finset.sum_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hmarg1, hmarg2,
    Finset.sum_sub_distrib, hprod_sum, hP1, sub_self] at hsum
  dsimp [shannonH]
  linarith

private lemma dist_prod_marg_fst {ι α β : Type*} [Fintype β]
    (I : Finset ι) (μ : ι → ℝ) (U : ι → α) (V : ι → β) (a : α) :
    ∑ b : β, dist I μ (fun n => (U n, V n)) (a, b) = dist I μ U a := by
  dsimp [dist]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : U n = a
  · simp [h]
  · simp [h]

private lemma dist_prod_marg_snd {ι α β : Type*} [Fintype α]
    (I : Finset ι) (μ : ι → ℝ) (U : ι → α) (V : ι → β) (b : β) :
    ∑ a : α, dist I μ (fun n => (U n, V n)) (a, b) = dist I μ V b := by
  dsimp [dist]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : V n = b
  · simp [h]
  · simp [h]

private lemma shannonH_cond_formula {ι α β : Type*} [Fintype α] [Fintype β]
    (I : Finset ι) (μ : ι → ℝ) (hμ0 : ∀ n ∈ I, 0 ≤ μ n) (U : ι → α) (V : ι → β) :
    shannonH (dist I μ (fun n => (U n, V n))) - shannonH (dist I μ U) =
      ∑ a ∈ Finset.univ.filter (fun a : α => 0 < dist I μ U a),
        dist I μ U a * shannonH (fun b : β => dist I μ (fun n => (U n, V n)) (a, b) / dist I μ U a) := by
  let P := dist I μ (fun n => (U n, V n))
  let PU := dist I μ U
  have hterm : ∀ a : α,
      (- ∑ b : β, P (a, b) * Real.log (P (a, b))) - (- (PU a * Real.log (PU a))) =
        if 0 < PU a then PU a * shannonH (fun b : β => P (a, b) / PU a) else 0 := by
    intro a
    have hmarg : ∑ b : β, P (a, b) = PU a := dist_prod_marg_fst I μ U V a
    have hP0 : ∀ b, 0 ≤ P (a, b) := fun b => dist_nonneg I μ hμ0 _ _
    have hPU0 : 0 ≤ PU a := dist_nonneg I μ hμ0 _ _
    split_ifs with ha
    · dsimp [shannonH]
      rw [mul_neg, Finset.mul_sum]
      have hinner : ∀ b : β,
          PU a * (P (a, b) / PU a * Real.log (P (a, b) / PU a)) =
            P (a, b) * Real.log (P (a, b)) - P (a, b) * Real.log (PU a) := by
        intro b
        rcases eq_or_lt_of_le (hP0 b) with hb0 | hb_pos
        · rw [← hb0]; simp
        · rw [Real.log_div hb_pos.ne' ha.ne']
          field_simp [ha.ne']
      simp_rw [hinner, Finset.sum_sub_distrib, ← Finset.sum_mul, hmarg]
      ring
    · have hPUeq : PU a = 0 := le_antisymm (not_lt.mp ha) hPU0
      have hPeq : ∀ b : β, P (a, b) = 0 := fun b => by
        have hle : P (a, b) ≤ ∑ b' : β, P (a, b') :=
          Finset.single_le_sum (fun b' _ => hP0 b') (Finset.mem_univ b)
        linarith [hP0 b]
      simp [hPUeq, hPeq]
  rw [Finset.sum_filter]
  dsimp [shannonH]
  rw [Fintype.sum_prod_type]
  calc (- ∑ a : α, ∑ b : β, P (a, b) * Real.log (P (a, b))) - (- ∑ a : α, PU a * Real.log (PU a))
      = ∑ a : α, ((- ∑ b : β, P (a, b) * Real.log (P (a, b))) - (- (PU a * Real.log (PU a)))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    _ = ∑ a : α, if 0 < PU a then PU a * shannonH (fun b : β => P (a, b) / PU a) else 0 :=
        Finset.sum_congr rfl fun a _ => hterm a

private lemma shannonH_mono {ι α β : Type*} [Fintype α] [Fintype β]
    (I : Finset ι) (μ : ι → ℝ) (hμ0 : ∀ n ∈ I, 0 ≤ μ n) (U : ι → α) (V : ι → β) :
    shannonH (dist I μ U) ≤ shannonH (dist I μ (fun n => (U n, V n))) := by
  have h := shannonH_cond_formula I μ hμ0 U V
  have hnn : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a : α => 0 < dist I μ U a),
      dist I μ U a * shannonH (fun b : β => dist I μ (fun n => (U n, V n)) (a, b) / dist I μ U a) := by
    refine Finset.sum_nonneg fun a ha => ?_
    have ha_pos : 0 < dist I μ U a := (Finset.mem_filter.mp ha).2
    refine mul_nonneg ha_pos.le (shannonH_nonneg _ ?_ ?_)
    · intro b; exact div_nonneg (dist_nonneg I μ hμ0 _ _) ha_pos.le
    · intro b
      rw [div_le_one ha_pos, ← dist_prod_marg_fst I μ U V a]
      exact Finset.single_le_sum (fun b' _ => dist_nonneg I μ hμ0 _ _) (Finset.mem_univ b)
  linarith

private lemma shannonH_cond_subadd {ι α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (I : Finset ι) (μ : ι → ℝ) (hμ0 : ∀ n ∈ I, 0 ≤ μ n)
    (U : ι → α) (V : ι → β) (W : ι → γ) :
    shannonH (dist I μ (fun n => (W n, (U n, V n)))) - shannonH (dist I μ W) ≤
      (shannonH (dist I μ (fun n => (W n, U n))) - shannonH (dist I μ W)) +
      (shannonH (dist I μ (fun n => (W n, V n))) - shannonH (dist I μ W)) := by
  rw [shannonH_cond_formula I μ hμ0 W (fun n => (U n, V n)),
      shannonH_cond_formula I μ hμ0 W U,
      shannonH_cond_formula I μ hμ0 W V,
      ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w hw => ?_
  have hw_pos : 0 < dist I μ W w := (Finset.mem_filter.mp hw).2
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hw_pos.le
  let Q : α × β → ℝ := fun ab => dist I μ (fun n => (W n, (U n, V n))) (w, ab) / dist I μ W w
  have hQ0 : ∀ ab, 0 ≤ Q ab := fun ab => div_nonneg (dist_nonneg I μ hμ0 _ _) hw_pos.le
  have hQ1 : ∑ ab : α × β, Q ab = 1 := by
    dsimp [Q]
    rw [← Finset.sum_div, dist_prod_marg_fst I μ W (fun n => (U n, V n)) w, div_self hw_pos.ne']
  have hsub := shannonH_subadd_dist Q hQ0 hQ1
  have hm1 : (fun a : α => ∑ b : β, Q (a, b)) =
      (fun a : α => dist I μ (fun n => (W n, U n)) (w, a) / dist I μ W w) := by
    funext a
    dsimp [Q]
    rw [← Finset.sum_div]
    congr 1
    dsimp [dist]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : W n = w ∧ U n = a
    · simp [h.1, h.2]
    · have h1 : ¬ ((W n, U n) = (w, a)) := fun he => h ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
      rw [if_neg h1]
      refine Finset.sum_eq_zero fun b _ => if_neg fun he => h ⟨congrArg Prod.fst he, congrArg (fun p => p.2.1) he⟩
  have hm2 : (fun b : β => ∑ a : α, Q (a, b)) =
      (fun b : β => dist I μ (fun n => (W n, V n)) (w, b) / dist I μ W w) := by
    funext b
    dsimp [Q]
    rw [← Finset.sum_div]
    congr 1
    dsimp [dist]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : W n = w ∧ V n = b
    · simp [h.1, h.2]
    · have h1 : ¬ ((W n, V n) = (w, b)) := fun he => h ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
      rw [if_neg h1]
      refine Finset.sum_eq_zero fun a _ => if_neg fun he => h ⟨congrArg Prod.fst he, congrArg (fun p => p.2.2) he⟩
  rw [hm1, hm2] at hsub
  exact hsub

private lemma shannonH_cond_fin_subadd {ι α γ : Type*} [Fintype α] [Fintype γ]
    (I : Finset ι) (μ : ι → ℝ) (hμ0 : ∀ n ∈ I, 0 ≤ μ n) (W : ι → γ) :
    ∀ (k : ℕ) (B : Fin k → ι → α),
      shannonH (dist I μ (fun n => (W n, fun m : Fin k => B m n))) - shannonH (dist I μ W) ≤
        ∑ m : Fin k, (shannonH (dist I μ (fun n => (W n, B m n))) - shannonH (dist I μ W)) := by
  intro k
  induction k with
  | zero =>
    intro B
    have heq : shannonH (dist I μ (fun n => (W n, fun m : Fin 0 => B m n))) = shannonH (dist I μ W) := by
      let e : γ ≃ γ × (Fin 0 → α) :=
        { toFun := fun w => (w, Fin.elim0)
          invFun := Prod.fst
          left_inv := fun _ => rfl
          right_inv := fun ⟨w, f⟩ => Prod.ext rfl (funext fun i => i.elim0) }
      have hcomp : (fun n => (W n, fun m : Fin 0 => B m n)) = e ∘ W := by
        funext n; exact Prod.ext rfl (funext fun i => i.elim0)
      rw [hcomp, shannonH_equiv]
    simp [heq]
  | succ k ih =>
    intro B
    let e : γ × (α × (Fin k → α)) ≃ γ × (Fin (k + 1) → α) :=
      Equiv.prodCongr (Equiv.refl γ) (Fin.snocEquiv (fun _ => α))
    have hcomp : (fun n => (W n, fun m : Fin (k + 1) => B m n)) =
        e ∘ (fun n => (W n, (B (Fin.last k) n, fun m : Fin k => B m.castSucc n))) := by
      funext n
      refine Prod.ext rfl (funext fun i => ?_)
      refine Fin.lastCases ?_ ?_ i
      · simp [e]
      · intro j; simp [e]
    rw [hcomp, shannonH_equiv]
    have hstep := shannonH_cond_subadd I μ hμ0
      (fun n => B (Fin.last k) n)
      (fun n => (fun m : Fin k => B m.castSucc n)) W
    have hih := ih (fun m => B m.castSucc)
    rw [Fin.sum_univ_castSucc]
    linarith

private lemma shannonH_diff_le {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∀ a, q a ≤ 1)
    {Δ : ℝ} (hΔ : ∀ a, |p a - q a| ≤ Δ) :
    |shannonH p - shannonH q| ≤ (Fintype.card α : ℝ) * (2 * Real.sqrt Δ) := by
  dsimp [shannonH]
  have hrew : (- ∑ a : α, p a * Real.log (p a)) - (- ∑ a : α, q a * Real.log (q a)) =
      ∑ a : α, ((-p a * Real.log (p a)) - (-q a * Real.log (q a))) := by
    rw [Finset.sum_sub_distrib]
    simp only [neg_mul, Finset.sum_neg_distrib]
  rw [hrew]
  calc |∑ a : α, ((-p a * Real.log (p a)) - (-q a * Real.log (q a)))|
      ≤ ∑ a : α, |(-p a * Real.log (p a)) - (-q a * Real.log (q a))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : α, (2 * Real.sqrt Δ) := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact (neg_mul_log_holder (hp0 a) (hp1 a) (hq0 a) (hq1 a)).trans
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hΔ a)) (by norm_num))
    _ = (Fintype.card α : ℝ) * (2 * Real.sqrt Δ) := by simp

/- ### Section 4: Logarithmic Shift Invariance and CRT Equidistribution -/

private lemma harmonic_sqrt_ge_one {X : ℕ} (hX : 100 ≤ X) :
    1 ≤ ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 : ℝ) / (n : ℝ) := by
  have h1 : (1 / 3 : ℝ) * Real.log (X : ℝ) ≤ ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) :=
    (OMA.R_Erdos67_erdos_67_R1.sum_inv_sqrt_bounds hX).1
  have hlog100 : 3 ≤ Real.log (X : ℝ) := by
    have hexp3 : Real.exp 3 ≤ (X : ℝ) := by
      have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      have h3 : Real.exp 3 = (Real.exp 1) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h27 : (Real.exp 1) ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le he 3
      have hX100 : (100 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      linarith
    have := Real.log_le_log (Real.exp_pos 3) hexp3
    rwa [Real.log_exp] at this
  linarith

private lemma real_log_shift_bound {X s : ℕ} (hX : 100 ≤ X) (hs : s ≤ Nat.sqrt X)
    (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hf1 : ∀ n, f n ≤ 1) :
    |(∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, f (n + s) / (n : ℝ)) -
      (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, f n / (n : ℝ))| ≤
    3 * (s : ℝ) / (Nat.sqrt X : ℝ) := by
  have hsq_ge10 : 10 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hsq_r : (0 : ℝ) < (Nat.sqrt X : ℝ) := by exact_mod_cast (show 0 < Nat.sqrt X by omega)
  have hov : Nat.sqrt X + 1 + s ≤ X := by
    have : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
    nlinarith
  have hreindex : ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, f (n + s) / (n : ℝ) =
      ∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) (X + s), f m / ((m - s : ℕ) : ℝ) := by
    refine Finset.sum_bij (fun n _ => n + s) ?_ ?_ ?_ ?_
    · intro n hn; rw [Finset.mem_Icc] at hn ⊢; omega
    · intro _ _ _ _ h; omega
    · intro m hm; rw [Finset.mem_Icc] at hm
      exact ⟨m - s, Finset.mem_Icc.mpr (by omega), by omega⟩
    · intro n _; simp
  rw [hreindex]
  have hS1 : Finset.Icc (Nat.sqrt X + 1 + s) (X + s) =
      Finset.Icc (Nat.sqrt X + 1 + s) X ∪ Finset.Icc (X + 1) (X + s) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hd1 : Disjoint (Finset.Icc (Nat.sqrt X + 1 + s) X) (Finset.Icc (X + 1) (X + s)) := by
    rw [Finset.disjoint_left]; intro m h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
  have hS2 : Finset.Icc (Nat.sqrt X + 1) X =
      Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s) ∪ Finset.Icc (Nat.sqrt X + 1 + s) X := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hd2 : Disjoint (Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s))
      (Finset.Icc (Nat.sqrt X + 1 + s) X) := by
    rw [Finset.disjoint_left]; intro m h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
  rw [hS1, Finset.sum_union hd1, hS2, Finset.sum_union hd2]
  have hrew : (∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m / ((m - s : ℕ) : ℝ)) +
      (∑ m ∈ Finset.Icc (X + 1) (X + s), f m / ((m - s : ℕ) : ℝ)) -
      ((∑ m ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), f m / (m : ℝ)) +
       (∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m / (m : ℝ))) =
      (∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m * (1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ))) +
      (∑ m ∈ Finset.Icc (X + 1) (X + s), f m / ((m - s : ℕ) : ℝ)) -
      (∑ m ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), f m / (m : ℝ)) := by
    have : ∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m * (1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ)) =
        (∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m / ((m - s : ℕ) : ℝ)) -
        (∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m / (m : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [this]; ring
  rw [hrew]
  have hB_ov : |∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X,
      f m * (1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ))| ≤ (s : ℝ) / (Nat.sqrt X : ℝ) := by
    have hnn_term : ∀ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X,
        0 ≤ f m * (1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ)) := fun m hm => by
      have hm' := Finset.mem_Icc.mp hm
      exact mul_nonneg (hf0 m) (sub_nonneg.mpr
        (one_div_le_one_div_of_le (by exact_mod_cast (show 0 < m - s by omega))
          (by exact_mod_cast Nat.sub_le m s)))
    rw [abs_of_nonneg (Finset.sum_nonneg hnn_term)]
    calc ∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m * (1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ))
        ≤ ∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, (1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' := Finset.mem_Icc.mp hm
          have hnn : 0 ≤ 1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ) := sub_nonneg.mpr
            (one_div_le_one_div_of_le (by exact_mod_cast (show 0 < m - s by omega))
              (by exact_mod_cast Nat.sub_le m s))
          exact mul_le_of_le_one_left hnn (hf1 m)
      _ ≤ (s : ℝ) / (Nat.sqrt X : ℝ) := by
          rw [Finset.sum_sub_distrib]
          have hsh : ∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, (1 : ℝ) / ((m - s : ℕ) : ℝ) =
              ∑ k ∈ Finset.Icc (Nat.sqrt X + 1) (X - s), (1 : ℝ) / (k : ℝ) := by
            refine Finset.sum_bij (fun m _ => m - s) ?_ ?_ ?_ ?_
            · intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
            · intro m₁ hm₁ m₂ hm₂ h; rw [Finset.mem_Icc] at hm₁ hm₂; omega
            · intro k hk; rw [Finset.mem_Icc] at hk
              exact ⟨k + s, Finset.mem_Icc.mpr (by omega), by omega⟩
            · intro _ _; rfl
          rw [hsh]
          have hsub1 : Finset.Icc (Nat.sqrt X + 1) (X - s) ⊆
              Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s) ∪ Finset.Icc (Nat.sqrt X + 1 + s) X := by
            intro k hk; rw [Finset.mem_Icc] at hk; simp only [Finset.mem_union, Finset.mem_Icc]; omega
          have hle1 : ∑ k ∈ Finset.Icc (Nat.sqrt X + 1) (X - s), (1 : ℝ) / (k : ℝ) ≤
              (∑ k ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), (1 : ℝ) / (k : ℝ)) +
              (∑ k ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, (1 : ℝ) / (k : ℝ)) := by
            rw [← Finset.sum_union hd2]
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun _ _ _ => by positivity
          have hhead : ∑ k ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), (1 : ℝ) / (k : ℝ) ≤
              (s : ℝ) / (Nat.sqrt X : ℝ) := by
            calc _ ≤ ∑ _k ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), (1 : ℝ) / (Nat.sqrt X : ℝ) := by
                  refine Finset.sum_le_sum fun k hk => one_div_le_one_div_of_le hsq_r
                    (by exact_mod_cast (show Nat.sqrt X ≤ k by have := (Finset.mem_Icc.mp hk).1; omega))
              _ = (s : ℝ) / (Nat.sqrt X : ℝ) := by
                  have hcard : (Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s)).card = s := by
                    simp [Nat.card_Icc]
                  simp [hcard, div_eq_mul_inv]
          linarith
  have hB_r : |∑ m ∈ Finset.Icc (X + 1) (X + s), f m / ((m - s : ℕ) : ℝ)| ≤
      (s : ℝ) / (Nat.sqrt X : ℝ) := by
    rw [abs_of_nonneg (Finset.sum_nonneg fun m _ => div_nonneg (hf0 m) (Nat.cast_nonneg _))]
    calc _ ≤ ∑ _m ∈ Finset.Icc (X + 1) (X + s), (1 : ℝ) / (Nat.sqrt X : ℝ) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' := Finset.mem_Icc.mp hm
          exact (div_le_div_of_nonneg_right (hf1 m) (Nat.cast_nonneg _)).trans
            (one_div_le_one_div_of_le hsq_r (by exact_mod_cast (show Nat.sqrt X ≤ m - s by omega)))
      _ = (s : ℝ) / (Nat.sqrt X : ℝ) := by
          have hcard : (Finset.Icc (X + 1) (X + s)).card = s := by simp [Nat.card_Icc]
          simp [hcard, div_eq_mul_inv]
  have hB_l : |∑ m ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), f m / (m : ℝ)| ≤
      (s : ℝ) / (Nat.sqrt X : ℝ) := by
    rw [abs_of_nonneg (Finset.sum_nonneg fun m _ => div_nonneg (hf0 m) (Nat.cast_nonneg _))]
    calc _ ≤ ∑ _m ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), (1 : ℝ) / (Nat.sqrt X : ℝ) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' := Finset.mem_Icc.mp hm
          exact (div_le_div_of_nonneg_right (hf1 m) (Nat.cast_nonneg _)).trans
            (one_div_le_one_div_of_le hsq_r (by exact_mod_cast (show Nat.sqrt X ≤ m by omega)))
      _ = (s : ℝ) / (Nat.sqrt X : ℝ) := by
          have hcard : (Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s)).card = s := by
            simp [Nat.card_Icc]
          simp [hcard, div_eq_mul_inv]
  have htri1 := abs_sub
    ((∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m * (1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ))) +
      ∑ m ∈ Finset.Icc (X + 1) (X + s), f m / ((m - s : ℕ) : ℝ))
    (∑ m ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), f m / (m : ℝ))
  have htri2 := abs_add_le
    (∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m * (1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ)))
    (∑ m ∈ Finset.Icc (X + 1) (X + s), f m / ((m - s : ℕ) : ℝ))
  have h3s : (s : ℝ) / (Nat.sqrt X : ℝ) + (s : ℝ) / (Nat.sqrt X : ℝ) + (s : ℝ) / (Nat.sqrt X : ℝ) =
      3 * (s : ℝ) / (Nat.sqrt X : ℝ) := by ring
  linarith [htri1, htri2, hB_ov, hB_r, hB_l, h3s]

private lemma exists_crt_shift (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (r : ℕ → ℕ) :
    ∃ s : ℕ, s < ∏ p ∈ S, p ∧ ∀ p ∈ S, (s : ZMod p) = (r p : ZMod p) := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨0, by simp, fun _ hp => absurd hp (Finset.notMem_empty _)⟩
  | @insert p S hpS ih =>
    have hp_prime : p.Prime := hS p (Finset.mem_insert_self p S)
    have hS_prime : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨s₀, hs₀_lt, hs₀_mod⟩ := ih hS_prime
    have hcop : Nat.Coprime p (∏ q ∈ S, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hne : p ≠ q := fun heq => hpS (heq ▸ hq)
      exact (Nat.coprime_primes hp_prime (hS_prime q hq)).mpr hne
    let cr := Nat.chineseRemainder hcop (r p) s₀
    have hprod_pos : 0 < p * ∏ q ∈ S, q :=
      Nat.mul_pos hp_prime.pos (Finset.prod_pos fun q hq => (hS_prime q hq).pos)
    refine ⟨cr.1 % (p * ∏ q ∈ S, q), ?_, ?_⟩
    · rw [Finset.prod_insert hpS]
      exact Nat.mod_lt _ hprod_pos
    · intro q hq
      rcases Finset.mem_insert.mp hq with hqp | hqS
      · subst hqp
        have h1 : cr.1 % (q * ∏ q' ∈ S, q') ≡ cr.1 [MOD q] :=
          (Nat.mod_modEq cr.1 (q * ∏ q' ∈ S, q')).of_dvd (dvd_mul_right q _)
        have h2 : cr.1 ≡ r q [MOD q] := cr.2.1
        exact (ZMod.natCast_eq_natCast_iff _ _ q).mpr (h1.trans h2)
      · have hq_dvd : q ∣ ∏ q' ∈ S, q' := Finset.dvd_prod_of_mem _ hqS
        have h1 : cr.1 % (p * ∏ q' ∈ S, q') ≡ cr.1 [MOD q] :=
          (Nat.mod_modEq cr.1 (p * ∏ q' ∈ S, q')).of_dvd (dvd_mul_of_dvd_right hq_dvd p)
        have h2 : cr.1 ≡ s₀ [MOD q] := cr.2.2.of_dvd hq_dvd
        have h3 : ((cr.1 % (p * ∏ q' ∈ S, q') : ℕ) : ZMod q) = (s₀ : ZMod q) :=
          (ZMod.natCast_eq_natCast_iff _ _ q).mpr (h1.trans h2)
        rw [h3, hs₀_mod q hqS]

/- ### Section 4b: Shift Invariance and Uniformity of `Y_H` under Logarithmic Weights -/

private def logWindow (X : ℕ) : Finset ℕ := Finset.Icc (Nat.sqrt X + 1) X

private noncomputable def logWeightSum (X : ℕ) : ℝ :=
  ∑ n ∈ logWindow X, (1 : ℝ) / (n : ℝ)

private noncomputable def logProb (X : ℕ) (n : ℕ) : ℝ :=
  (1 / logWeightSum X) * (1 / (n : ℝ))

private lemma logWeightSum_ge_one {X : ℕ} (hX : 100 ≤ X) : 1 ≤ logWeightSum X :=
  harmonic_sqrt_ge_one hX

private lemma logProb_nonneg {X : ℕ} (hX : 100 ≤ X) (n : ℕ) : 0 ≤ logProb X n := by
  have hL : 0 < logWeightSum X := lt_of_lt_of_le zero_lt_one (logWeightSum_ge_one hX)
  dsimp [logProb]
  positivity

private lemma sum_logProb_eq_one {X : ℕ} (hX : 100 ≤ X) :
    ∑ n ∈ logWindow X, logProb X n = 1 := by
  have hL : 0 < logWeightSum X := lt_of_lt_of_le zero_lt_one (logWeightSum_ge_one hX)
  dsimp [logProb]
  rw [← Finset.mul_sum]
  change (1 / logWeightSum X) * logWeightSum X = 1
  field_simp [hL.ne']

private lemma dist_shift_abs_le {α : Type*} {X s : ℕ} (hX : 100 ≤ X) (hs : s ≤ Nat.sqrt X)
    (W : ℕ → α) (a : α) :
    |dist (logWindow X) (logProb X) (fun n => W (n + s)) a -
      dist (logWindow X) (logProb X) W a| ≤ 3 * (s : ℝ) / (Nat.sqrt X : ℝ) := by
  have hL1 : 1 ≤ logWeightSum X := logWeightSum_ge_one hX
  have hL_pos : 0 < logWeightSum X := lt_of_lt_of_le zero_lt_one hL1
  let ind : ℕ → ℝ := fun n => if W n = a then 1 else 0
  have hind0 : ∀ n, 0 ≤ ind n := fun n => by dsimp [ind]; split_ifs <;> norm_num
  have hind1 : ∀ n, ind n ≤ 1 := fun n => by dsimp [ind]; split_ifs <;> norm_num
  have h1 : dist (logWindow X) (logProb X) (fun n => W (n + s)) a =
      (1 / logWeightSum X) * ∑ n ∈ logWindow X, ind (n + s) / (n : ℝ) := by
    dsimp [dist, logProb, ind]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  have h2 : dist (logWindow X) (logProb X) W a =
      (1 / logWeightSum X) * ∑ n ∈ logWindow X, ind n / (n : ℝ) := by
    dsimp [dist, logProb, ind]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  rw [h1, h2, ← mul_sub, abs_mul, abs_of_pos (one_div_pos.mpr hL_pos)]
  have hsh := real_log_shift_bound hX hs ind hind0 hind1
  have hinv_le1 : 1 / logWeightSum X ≤ 1 := (div_le_one hL_pos).mpr hL1
  calc (1 / logWeightSum X) * |(∑ n ∈ logWindow X, ind (n + s) / (n : ℝ)) -
          (∑ n ∈ logWindow X, ind n / (n : ℝ))|
      ≤ 1 * (3 * (s : ℝ) / (Nat.sqrt X : ℝ)) :=
        mul_le_mul hinv_le1 hsh (abs_nonneg _) zero_le_one
    _ = 3 * (s : ℝ) / (Nat.sqrt X : ℝ) := one_mul _

private lemma shannonH_shift_abs_le {α : Type*} [Fintype α] {X s : ℕ}
    (hX : 100 ≤ X) (hs : s ≤ Nat.sqrt X) (W : ℕ → α) :
    |shannonH (dist (logWindow X) (logProb X) (fun n => W (n + s))) -
      shannonH (dist (logWindow X) (logProb X) W)| ≤
    (Fintype.card α : ℝ) * (2 * Real.sqrt (3 * (s : ℝ) / (Nat.sqrt X : ℝ))) := by
  refine shannonH_diff_le _ _
    (fun a => dist_nonneg _ _ (fun n _ => logProb_nonneg hX n) _ a)
    (fun a => dist_le_one _ _ (fun n _ => logProb_nonneg hX n) (sum_logProb_eq_one hX) _ a)
    (fun a => dist_nonneg _ _ (fun n _ => logProb_nonneg hX n) _ a)
    (fun a => dist_le_one _ _ (fun n _ => logProb_nonneg hX n) (sum_logProb_eq_one hX) _ a)
    (fun a => dist_shift_abs_le hX hs W a)

private lemma shannonH_Y_near_uniform {X : ℕ} (S : Finset ℕ)
    (hX : 100 ≤ X) (hS : ∀ p ∈ S, p.Prime)
    [∀ p : S, NeZero p.1]
    (hQ_le : ∏ p ∈ S, p ≤ Nat.sqrt X) :
    |shannonH (dist (logWindow X) (logProb X) (fun n (p : S) => (n : ZMod p.1))) -
      Real.log ((∏ p ∈ S, p : ℕ) : ℝ)| ≤
      ((∏ p ∈ S, p : ℕ) : ℝ) * (2 * Real.sqrt (3 * ((∏ p ∈ S, p : ℕ) : ℝ) / (Nat.sqrt X : ℝ))) := by
  set Ω := ∀ p : S, ZMod p.1
  let Y : ℕ → Ω := fun n p => (n : ZMod p.1)
  change |shannonH (dist (logWindow X) (logProb X) Y) - Real.log ((∏ p ∈ S, p : ℕ) : ℝ)| ≤ _
  have hcardΩ : Fintype.card Ω = ∏ p ∈ S, p := by
    dsimp [Ω]
    rw [Fintype.card_pi]
    calc ∏ p : S, Fintype.card (ZMod p.1)
        = ∏ p : S, p.1 := Finset.prod_congr rfl fun p _ => ZMod.card p.1
      _ = ∏ p ∈ S, p := Finset.prod_coe_sort S (fun p => p)
  have hQ_pos : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS p hp).pos
  have hcardΩ_pos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by rw [hcardΩ]; exact_mod_cast hQ_pos
  have hpair : ∀ y y' : Ω,
      |dist (logWindow X) (logProb X) Y y - dist (logWindow X) (logProb X) Y y'| ≤
        3 * ((∏ p ∈ S, p : ℕ) : ℝ) / (Nat.sqrt X : ℝ) := by
    intro y y'
    let r : ℕ → ℕ := fun q => if hq : q ∈ S then (y' ⟨q, hq⟩ - y ⟨q, hq⟩).val else 0
    obtain ⟨s, hs_lt, hs_mod⟩ := exists_crt_shift S hS r
    have hs_le : s ≤ Nat.sqrt X := (le_of_lt hs_lt).trans hQ_le
    have hshift_eq : dist (logWindow X) (logProb X) Y y =
        dist (logWindow X) (logProb X) (fun n => Y (n + s)) y' := by
      dsimp [dist]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hiff : Y n = y ↔ Y (n + s) = y' := by
        constructor <;> intro heq <;> funext p
        · have hs_p : (s : ZMod p.1) = y' p - y p := by
            have h1 := hs_mod p.1 p.2
            dsimp [r] at h1
            rw [dif_pos p.2, ZMod.natCast_zmod_val] at h1
            exact h1
          have hnp : Y n p = y p := congrFun heq p
          dsimp [Y] at hnp ⊢
          rw [Nat.cast_add, hnp, hs_p, add_sub_cancel]
        · have hs_p : (s : ZMod p.1) = y' p - y p := by
            have h1 := hs_mod p.1 p.2
            dsimp [r] at h1
            rw [dif_pos p.2, ZMod.natCast_zmod_val] at h1
            exact h1
          have hnp : Y (n + s) p = y' p := congrFun heq p
          dsimp [Y] at hnp ⊢
          rw [Nat.cast_add, hs_p] at hnp
          exact add_right_cancel (hnp.trans (add_sub_cancel (y p) (y' p)).symm)
      by_cases h : Y n = y
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
    rw [hshift_eq]
    have hbd := dist_shift_abs_le hX hs_le Y y'
    refine hbd.trans ?_
    gcongr
  let unif : Ω → ℝ := fun _ => 1 / (Fintype.card Ω : ℝ)
  have hunif_H : shannonH unif = Real.log ((∏ p ∈ S, p : ℕ) : ℝ) := by
    dsimp [shannonH, unif]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div, Real.log_inv]
    rw [hcardΩ]
    have hQ_r : ((∏ p ∈ S, p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hQ_pos.ne'
    field_simp [hQ_r]
  have hdiff_unif : ∀ y : Ω,
      |dist (logWindow X) (logProb X) Y y - unif y| ≤
        3 * ((∏ p ∈ S, p : ℕ) : ℝ) / (Nat.sqrt X : ℝ) := by
    intro y
    have hsum1 : ∑ y' : Ω, dist (logWindow X) (logProb X) Y y' = 1 :=
      sum_dist_eq_one _ _ (sum_logProb_eq_one hX) Y
    have hrew : dist (logWindow X) (logProb X) Y y - unif y =
        (1 / (Fintype.card Ω : ℝ)) *
          ∑ y' : Ω, (dist (logWindow X) (logProb X) Y y - dist (logWindow X) (logProb X) Y y') := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum1]
      dsimp [unif]
      field_simp [hcardΩ_pos.ne']
    rw [hrew, abs_mul, abs_of_pos (one_div_pos.mpr hcardΩ_pos)]
    calc (1 / (Fintype.card Ω : ℝ)) *
          |∑ y' : Ω, (dist (logWindow X) (logProb X) Y y - dist (logWindow X) (logProb X) Y y')|
        ≤ (1 / (Fintype.card Ω : ℝ)) *
          ∑ y' : Ω, |dist (logWindow X) (logProb X) Y y - dist (logWindow X) (logProb X) Y y'| := by
          gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (1 / (Fintype.card Ω : ℝ)) *
          ∑ _y' : Ω, (3 * ((∏ p ∈ S, p : ℕ) : ℝ) / (Nat.sqrt X : ℝ)) := by
          gcongr with y' _; exact hpair y y'
      _ = 3 * ((∏ p ∈ S, p : ℕ) : ℝ) / (Nat.sqrt X : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp [hcardΩ_pos.ne']
  rw [← hunif_H]
  have hsh := shannonH_diff_le (dist (logWindow X) (logProb X) Y) unif
    (fun y => dist_nonneg _ _ (fun n _ => logProb_nonneg hX n) _ y)
    (fun y => dist_le_one _ _ (fun n _ => logProb_nonneg hX n) (sum_logProb_eq_one hX) _ y)
    (fun _ => by dsimp [unif]; positivity)
    (fun _ => by
      dsimp [unif]; rw [div_le_one hcardΩ_pos]
      rw [hcardΩ]; exact_mod_cast hQ_pos)
    hdiff_unif
  simpa only [hcardΩ] using hsh

/- ### Section 5: Hoeffding + Gibbs Bilinear Decoupling Bound -/

private noncomputable def evalBlock {H : ℕ} {Alph : Type*} (val : Alph → ℂ)
    (x : Fin H → Alph) (k : ℕ) : ℂ :=
  if hk : 1 ≤ k ∧ k ≤ H then val (x ⟨k - 1, by omega⟩) else 0

private def blockOf (H : ℕ) {Alph : Type*} (f : ℕ → Alph) (n : ℕ) : Fin H → Alph :=
  fun j => f (n + j.val + 1)

private lemma evalBlock_blockOf {H : ℕ} {Alph : Type*} (val : Alph → ℂ) (f : ℕ → Alph)
    (n k : ℕ) (hk1 : 1 ≤ k) (hkH : k ≤ H) :
    evalBlock val (blockOf H f n) k = val (f (n + k)) := by
  dsimp [evalBlock, blockOf]
  rw [if_pos ⟨hk1, hkH⟩]
  have heq : n + (k - 1) + 1 = n + k := by omega
  rw [heq]

private lemma evalBlock_norm_le {H : ℕ} {Alph : Type*} (val : Alph → ℂ)
    (hval : ∀ s : Alph, ‖val s‖ ≤ 2) (x : Fin H → Alph) (k : ℕ) :
    ‖evalBlock val x k‖ ≤ 2 := by
  dsimp [evalBlock]
  split_ifs
  · exact hval _
  · simp

private noncomputable def F_prime (h H : ℕ) {Alph : Type*} (val : Alph → ℂ)
    (x : Fin H → Alph) (p : ℕ) (a : ZMod p) : ℂ :=
  ∑ j ∈ Finset.Icc 1 H,
    if j + p * h ≤ H then
      ((if a + (j : ZMod p) = 0 then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
        evalBlock val x j * star (evalBlock val x (j + p * h))
    else 0

private lemma F_prime_eq_on_block (h H : ℕ) {Alph : Type*} (val : Alph → ℂ) (f : ℕ → Alph)
    (n p : ℕ) :
    F_prime h H val (blockOf H f n) p (n : ZMod p) =
      ∑ j ∈ Finset.Icc 1 H,
        if j + p * h ≤ H then
          ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
            val (f (n + j)) * star (val (f (n + j + p * h)))
        else 0 := by
  dsimp [F_prime]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjI := Finset.mem_Icc.mp hj
  by_cases hjp : j + p * h ≤ H
  · rw [if_pos hjp, if_pos hjp]
    have h1 := evalBlock_blockOf val f n j hjI.1 hjI.2
    have h2 := evalBlock_blockOf val f n (j + p * h) (by omega) hjp
    rw [h1, h2, Nat.add_assoc]
    have hdvd_iff : (n : ZMod p) + (j : ZMod p) = 0 ↔ p ∣ n + j := by
      rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    by_cases hd : p ∣ n + j
    · rw [if_pos (hdvd_iff.mpr hd), if_pos hd]
    · rw [if_neg (fun h' => hd (hdvd_iff.mp h')), if_neg hd]
  · rw [if_neg hjp, if_neg hjp]

private lemma F_prime_sum_eq_zero (h H : ℕ) {Alph : Type*} (val : Alph → ℂ)
    (x : Fin H → Alph) (p : ℕ) [NeZero p] :
    ∑ a : ZMod p, F_prime h H val x p a = 0 := by
  dsimp [F_prime]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hjp : j + p * h ≤ H
  · simp_rw [if_pos hjp]
    trans (∑ a : ZMod p, ((if a + (j : ZMod p) = 0 then (1 : ℂ) else 0) - 1 / (p : ℂ))) *
        (evalBlock val x j * (starRingEnd ℂ) (evalBlock val x (j + p * h)))
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => by ring
    · have hinner : ∑ a : ZMod p, ((if a + (j : ZMod p) = 0 then (1 : ℂ) else 0) - 1 / (p : ℂ)) = 0 := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        have h1 : ∑ a : ZMod p, (if a + (j : ZMod p) = 0 then (1 : ℂ) else 0) = 1 := by
          rw [Finset.sum_eq_single (-(j : ZMod p))]
          · simp
          · intro a _ hne
            rw [if_neg]
            intro heq
            exact hne (eq_neg_of_add_eq_zero_left heq)
          · intro h; exact absurd (Finset.mem_univ _) h
        have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
        rw [h1]
        field_simp [hp_ne]
        ring
      rw [hinner, zero_mul]
  · simp_rw [if_neg hjp]; simp

private lemma card_dvd_Icc_le (m H p : ℕ) (hp : 1 ≤ p) :
    ((Finset.Icc 1 H).filter (fun j => p ∣ m + j)).card ≤ H / p + 1 := by
  let S := (Finset.Icc 1 H).filter (fun j => p ∣ m + j)
  have hinj : S.card ≤ (Finset.Icc (m / p + 1) ((m + H) / p)).card := by
    refine Finset.card_le_card_of_injOn (fun j => (m + j) / p) ?_ ?_
    · intro j hj
      have hj1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1
      have hdvd := (Finset.mem_filter.mp hj).2
      have hmul := Nat.mul_div_cancel' hdvd
      rw [Finset.mem_coe, Finset.mem_Icc]
      constructor
      · by_contra hlt
        push Not at hlt
        have hle : (m + j) / p ≤ m / p := by omega
        have h1 : p * ((m + j) / p) ≤ p * (m / p) := Nat.mul_le_mul_left p hle
        have h2 : p * (m / p) ≤ m := Nat.mul_div_le m p
        omega
      · exact Nat.div_le_div_right (by omega)
    · intro j₁ hj₁ j₂ hj₂ hEq
      have h1 := Nat.mul_div_cancel' (Finset.mem_filter.mp hj₁).2
      have h2 := Nat.mul_div_cancel' (Finset.mem_filter.mp hj₂).2
      dsimp only at hEq
      rw [hEq] at h1
      omega
  have hcard : (Finset.Icc (m / p + 1) ((m + H) / p)).card = (m + H) / p - m / p := by
    rw [Nat.card_Icc]; omega
  have hdiv_add : (m + H) / p ≤ m / p + H / p + 1 := by
    have h1 := Nat.div_add_mod m p
    have h2 := Nat.div_add_mod H p
    have h3 := Nat.mod_lt m (by omega : 0 < p)
    have h4 := Nat.mod_lt H (by omega : 0 < p)
    have h5 : m + H < p * (m / p + H / p + 2) := by nlinarith
    have h6 : (m + H) / p < m / p + H / p + 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
    omega
  have hmono : m / p ≤ (m + H) / p := Nat.div_le_div_right (Nat.le_add_right m H)
  change S.card ≤ H / p + 1
  omega

private lemma sum_abs_dvd_sub_inv_le (m H p : ℕ) (hp : 1 ≤ p) (hpH : p ≤ H) :
    ∑ j ∈ Finset.Icc 1 H, ‖(if p ∣ m + j then (1 : ℂ) else 0) - 1 / (p : ℂ)‖ ≤
      3 * (H : ℝ) / (p : ℝ) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  calc ∑ j ∈ Finset.Icc 1 H, ‖(if p ∣ m + j then (1 : ℂ) else 0) - 1 / (p : ℂ)‖
      ≤ ∑ j ∈ Finset.Icc 1 H, ((if p ∣ m + j then (1 : ℝ) else 0) + 1 / (p : ℝ)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have htri := norm_sub_le (if p ∣ m + j then (1 : ℂ) else 0) (1 / (p : ℂ))
        have h1 : ‖if p ∣ m + j then (1 : ℂ) else 0‖ = if p ∣ m + j then (1 : ℝ) else 0 := by
          split_ifs <;> simp
        have h2 : ‖(1 : ℂ) / (p : ℂ)‖ = 1 / (p : ℝ) := by simp
        linarith
    _ = (((Finset.Icc 1 H).filter (fun j => p ∣ m + j)).card : ℝ) + (H : ℝ) / (p : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp [Nat.card_Icc, div_eq_mul_inv]
    _ ≤ ((H / p + 1 : ℕ) : ℝ) + (H : ℝ) / (p : ℝ) := by
        gcongr; exact_mod_cast card_dvd_Icc_le m H p hp
    _ ≤ 2 * (H : ℝ) / (p : ℝ) + (H : ℝ) / (p : ℝ) := by
        have hdiv : ((H / p : ℕ) : ℝ) ≤ (H : ℝ) / (p : ℝ) := by
          rw [le_div_iff₀ hp_pos]
          exact_mod_cast Nat.div_mul_le_self H p
        have h1le : (1 : ℝ) ≤ (H : ℝ) / (p : ℝ) := (one_le_div hp_pos).mpr (by exact_mod_cast hpH)
        have h2eq : 2 * (H : ℝ) / (p : ℝ) = (H : ℝ) / (p : ℝ) + (H : ℝ) / (p : ℝ) := by ring
        push_cast; linarith
    _ = 3 * (H : ℝ) / (p : ℝ) := by ring

private lemma F_prime_norm_le (h H : ℕ) {Alph : Type*} (val : Alph → ℂ)
    (hval : ∀ s : Alph, ‖val s‖ ≤ 2) (x : Fin H → Alph)
    (p : ℕ) (hp : 1 ≤ p) (hpH : p ≤ H) (a : ZMod p) :
    ‖F_prime h H val x p a‖ ≤ 12 * (H : ℝ) / (p : ℝ) := by
  have : NeZero p := ⟨by omega⟩
  dsimp [F_prime]
  calc ‖∑ j ∈ Finset.Icc 1 H, _‖
      ≤ ∑ j ∈ Finset.Icc 1 H, ‖if j + p * h ≤ H then
          ((if a + (j : ZMod p) = 0 then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
            evalBlock val x j * star (evalBlock val x (j + p * h)) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 H, 4 * ‖(if p ∣ a.val + j then (1 : ℂ) else 0) - 1 / (p : ℂ)‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hjp : j + p * h ≤ H
        · rw [if_pos hjp]
          have hdvd_iff : a + (j : ZMod p) = 0 ↔ p ∣ a.val + j := by
            have ha : (a.val : ZMod p) = a := ZMod.natCast_zmod_val a
            conv_lhs => rw [← ha]
            rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
          have hif : (if a + (j : ZMod p) = 0 then (1 : ℂ) else 0) =
              (if p ∣ a.val + j then (1 : ℂ) else 0) := by
            by_cases hd : p ∣ a.val + j
            · rw [if_pos (hdvd_iff.mpr hd), if_pos hd]
            · rw [if_neg (fun h' => hd (hdvd_iff.mp h')), if_neg hd]
          rw [hif, norm_mul, norm_mul, norm_star]
          have h1 := evalBlock_norm_le val hval x j
          have h2 := evalBlock_norm_le val hval x (j + p * h)
          have hprod : ‖evalBlock val x j‖ * ‖evalBlock val x (j + p * h)‖ ≤ 4 := by
            have := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
            linarith
          have hnn := norm_nonneg ((if p ∣ a.val + j then (1 : ℂ) else 0) - 1 / (p : ℂ))
          calc ‖_‖ * ‖evalBlock val x j‖ * ‖evalBlock val x (j + p * h)‖
              = ‖_‖ * (‖evalBlock val x j‖ * ‖evalBlock val x (j + p * h)‖) := by ring
            _ ≤ ‖_‖ * 4 := mul_le_mul_of_nonneg_left hprod hnn
            _ = 4 * ‖_‖ := mul_comm _ _
        · rw [if_neg hjp, norm_zero]; positivity
    _ = 4 * ∑ j ∈ Finset.Icc 1 H, ‖(if p ∣ a.val + j then (1 : ℂ) else 0) - 1 / (p : ℂ)‖ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ 4 * (3 * (H : ℝ) / (p : ℝ)) := by gcongr; exact sum_abs_dvd_sub_inv_le a.val H p hp hpH
    _ = 12 * (H : ℝ) / (p : ℝ) := by ring

private lemma hoeffding_product_mgf (h H : ℕ) {δ : ℝ} {Alph : Type*}
    (val : Alph → ℂ) (hval : ∀ s : Alph, ‖val s‖ ≤ 2)
    (hδ0 : 0 < δ) (hδ14 : δ ≤ 1 / 4) (hH : (16 / δ ^ 2 + 100 : ℝ) ≤ (H : ℝ))
    [∀ p : primeWindow δ H, NeZero p.1]
    (proj : ℂ →ₗ[ℝ] ℝ) (hproj_le : ∀ z : ℂ, |proj z| ≤ ‖z‖)
    (x : Fin H → Alph) (t : ℝ) :
    let P := primeWindow δ H
    let Ω := ∀ p : P, ZMod p.1
    let F : Ω → ℂ := fun y => ∑ p : P, F_prime h H val x p.1 (y p)
    (1 / (Fintype.card Ω : ℝ)) * ∑ y : Ω, Real.exp (t * proj (F y)) ≤
      Real.exp (t ^ 2 * (1728 * (H : ℝ) / (δ * Real.log (H : ℝ))) / 2) := by
  intro P Ω F
  have hcheb := chebyshev_P_H_bounds hδ0 hδ14 hH
  have hH_pos : (0 : ℝ) < (H : ℝ) := by
    have : 0 < 16 / δ ^ 2 := by positivity
    linarith
  have hcardΩ : (Fintype.card Ω : ℝ) = ∏ p : P, (p.1 : ℝ) := by
    dsimp [Ω]
    rw [Fintype.card_pi, Nat.cast_prod]
    exact Finset.prod_congr rfl fun p _ => by rw [ZMod.card]
  have hfact : (1 / (Fintype.card Ω : ℝ)) * ∑ y : Ω, Real.exp (t * proj (F y)) =
      ∏ p : P, ((1 / (p.1 : ℝ)) * ∑ a : ZMod p.1, Real.exp (t * proj (F_prime h H val x p.1 a))) := by
    have hexp : ∀ y : Ω, Real.exp (t * proj (F y)) =
        ∏ p : P, Real.exp (t * proj (F_prime h H val x p.1 (y p))) := by
      intro y
      dsimp [F]
      rw [map_sum, Finset.mul_sum, Real.exp_sum]
    simp_rw [hexp]
    rw [← Fintype.prod_sum (fun (p : P) (a : ZMod p.1) =>
      Real.exp (t * proj (F_prime h H val x p.1 a)))]
    rw [hcardΩ, one_div, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => by ring
  rw [hfact]
  have hle_prod : ∏ p : P, ((1 / (p.1 : ℝ)) * ∑ a : ZMod p.1, Real.exp (t * proj (F_prime h H val x p.1 a))) ≤
      ∏ p : P, Real.exp (t ^ 2 * (12 * (H : ℝ) / (p.1 : ℝ)) ^ 2 / 2) := by
    refine Finset.prod_le_prod (fun p _ => by positivity) fun p _ => ?_
    have hp_mem := Finset.mem_filter.mp p.2
    have hp_prime : p.1.Prime := hp_mem.2
    have hp_le_dH : (p.1 : ℝ) ≤ δ * (H : ℝ) :=
      (by exact_mod_cast (Finset.mem_Icc.mp hp_mem.1).2 : (p.1 : ℝ) ≤ (Nat.floor (δ * (H : ℝ)) : ℝ)).trans
        (Nat.floor_le (by positivity))
    have hp_le_H : p.1 ≤ H := by
      have : (p.1 : ℝ) ≤ (H : ℝ) := hp_le_dH.trans (by nlinarith)
      exact_mod_cast this
    have hmean : ∑ a : ZMod p.1, proj (F_prime h H val x p.1 a) = 0 := by
      rw [← map_sum, F_prime_sum_eq_zero, map_zero]
    have hbd : ∀ a : ZMod p.1, |proj (F_prime h H val x p.1 a)| ≤ 12 * (H : ℝ) / (p.1 : ℝ) := fun a =>
      (hproj_le _).trans (F_prime_norm_le h H val hval x p.1 hp_prime.one_le hp_le_H a)
    have hmgf := hoeffding_mgf (fun a : ZMod p.1 => proj (F_prime h H val x p.1 a))
      (12 * (H : ℝ) / (p.1 : ℝ)) (by positivity) hmean hbd t
    simpa only [ZMod.card] using hmgf
  refine hle_prod.trans ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  have hsum_eq : ∑ p : P, t ^ 2 * (12 * (H : ℝ) / (p.1 : ℝ)) ^ 2 / 2 =
      t ^ 2 * (144 * (H : ℝ) ^ 2 * ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) ^ 2)) / 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    rw [← Finset.sum_coe_sort P (fun p => t ^ 2 * (144 * (H : ℝ) ^ 2 * (1 / (p : ℝ) ^ 2)) / 2)]
    refine Finset.sum_congr rfl fun p _ => by ring
  rw [hsum_eq]
  have hV_le : 144 * (H : ℝ) ^ 2 * ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) ^ 2) ≤
      1728 * (H : ℝ) / (δ * Real.log (H : ℝ)) := by
    calc 144 * (H : ℝ) ^ 2 * ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) ^ 2)
        ≤ 144 * (H : ℝ) ^ 2 * (12 / (δ * (H : ℝ) * Real.log (H : ℝ))) := by gcongr; exact hcheb.2.2.2
      _ = 1728 * (H : ℝ) / (δ * Real.log (H : ℝ)) := by
          have hlogH : 0 < Real.log (H : ℝ) := by linarith [hcheb.1]
          field_simp [hδ0.ne', hH_pos.ne', hlogH.ne']; ring
  gcongr

private lemma bilinear_decoupling_bound (h H X : ℕ) {δ : ℝ} {Alph : Type*} [Fintype Alph] [Nonempty Alph]
    (val : Alph → ℂ) (hval : ∀ s : Alph, ‖val s‖ ≤ 2) (f : ℕ → Alph)
    (hδ0 : 0 < δ) (hδ14 : δ ≤ 1 / 4) (hH : (16 / δ ^ 2 + 100 : ℝ) ≤ (H : ℝ))
    (hX : 100 ≤ X)
    [∀ p : primeWindow δ H, NeZero p.1] :
    let P := primeWindow δ H
    let Ω := ∀ p : P, ZMod p.1
    let XH : ℕ → (Fin H → Alph) := blockOf H f
    let YH : ℕ → Ω := fun n p => (n : ZMod p.1)
    let V : ℝ := 1728 * (H : ℝ) / (δ * Real.log (H : ℝ))
    let D_H : ℝ := Real.log (Fintype.card Ω : ℝ) -
      (shannonH (dist (logWindow X) (logProb X) (fun n => (XH n, YH n))) -
       shannonH (dist (logWindow X) (logProb X) XH))
    ‖(1 / (logWeightSum X : ℂ)) * ∑ n ∈ logWindow X, (1 / (n : ℂ)) *
      ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 H,
        if j + p * h ≤ H then
          ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
            val (f (n + j)) * star (val (f (n + j + p * h)))
        else 0‖ ^ 2 ≤ 4 * V * D_H := by
  intro P Ω XH YH V D_H
  have hcheb := chebyshev_P_H_bounds hδ0 hδ14 hH
  have hH_pos : (0 : ℝ) < (H : ℝ) := by
    have : 0 < 16 / δ ^ 2 := by positivity
    linarith
  have hlogH_pos : 0 < Real.log (H : ℝ) := by linarith [hcheb.1]
  have hV_pos : 0 < V := by dsimp [V]; positivity
  let F : (Fin H → Alph) → Ω → ℂ := fun x y => ∑ p : P, F_prime h H val x p.1 (y p)
  let Z : ℂ := (1 / (logWeightSum X : ℂ)) * ∑ n ∈ logWindow X, (1 / (n : ℂ)) *
      ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 H,
        if j + p * h ≤ H then
          ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
            val (f (n + j)) * star (val (f (n + j + p * h)))
        else 0
  have hZ_eq : Z = ∑ n ∈ logWindow X, (logProb X n : ℂ) * F (XH n) (YH n) := by
    have hinner : ∀ n : ℕ,
        (∑ p ∈ P, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
              val (f (n + j)) * (starRingEnd ℂ) (val (f (n + j + p * h)))
          else 0) = F (XH n) (YH n) := by
      intro n
      dsimp [F]
      rw [← Finset.sum_coe_sort P]
      refine Finset.sum_congr rfl fun p _ => ?_
      simpa only [Complex.star_def] using (F_prime_eq_on_block h H val f n p.1).symm
    dsimp [Z, logProb]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hinner n]
    push_cast
    ring
  have hproj_sq : ∀ (proj : ℂ →ₗ[ℝ] ℝ) (hproj_le : ∀ z : ℂ, |proj z| ≤ ‖z‖),
      (proj Z) ^ 2 ≤ 2 * V * D_H := by
    intro proj hproj_le
    set u : ℝ := proj Z
    have hu_eq : u = ∑ n ∈ logWindow X, logProb X n * proj (F (XH n) (YH n)) := by
      dsimp [u]; rw [hZ_eq, map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hsm : ((logProb X n : ℂ) * F (XH n) (YH n)) = (logProb X n) • F (XH n) (YH n) := by
        rw [Complex.real_smul]
      rw [hsm, map_smul, smul_eq_mul]
    let PX := dist (logWindow X) (logProb X) XH
    let PXY := dist (logWindow X) (logProb X) (fun n => (XH n, YH n))
    have hu_group : u = ∑ x ∈ Finset.univ.filter (fun x : Fin H → Alph => 0 < PX x),
        PX x * ∑ y : Ω, (PXY (x, y) / PX x) * proj (F x y) := by
      rw [hu_eq]
      have h1 : ∑ n ∈ logWindow X, logProb X n * proj (F (XH n) (YH n)) =
          ∑ x : Fin H → Alph, ∑ y : Ω, PXY (x, y) * proj (F x y) := by
        calc ∑ n ∈ logWindow X, logProb X n * proj (F (XH n) (YH n))
            = ∑ n ∈ logWindow X, ∑ x : Fin H → Alph, ∑ y : Ω,
                (if (XH n, YH n) = (x, y) then logProb X n else 0) * proj (F x y) := by
              refine Finset.sum_congr rfl fun n _ => ?_
              rw [Finset.sum_eq_single (XH n)]
              · rw [Finset.sum_eq_single (YH n)]
                · simp
                · intro y _ hne; simp [hne.symm]
                · intro h; exact absurd (Finset.mem_univ _) h
              · intro x _ hne
                refine Finset.sum_eq_zero fun y _ => ?_
                have : ¬ ((XH n, YH n) = (x, y)) := fun he => hne (congrArg Prod.fst he).symm
                simp [this]
              · intro h; exact absurd (Finset.mem_univ _) h
          _ = ∑ x : Fin H → Alph, ∑ n ∈ logWindow X, ∑ y : Ω,
                (if (XH n, YH n) = (x, y) then logProb X n else 0) * proj (F x y) := Finset.sum_comm
          _ = ∑ x : Fin H → Alph, ∑ y : Ω, ∑ n ∈ logWindow X,
                (if (XH n, YH n) = (x, y) then logProb X n else 0) * proj (F x y) :=
              Finset.sum_congr rfl fun x _ => Finset.sum_comm
          _ = ∑ x : Fin H → Alph, ∑ y : Ω, PXY (x, y) * proj (F x y) := by
              refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
              dsimp only [PXY, dist]
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun n _ => ?_
              by_cases h : (XH n, YH n) = (x, y) <;> simp [h]
      rw [h1, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hPX0 : 0 ≤ PX x := dist_nonneg _ _ (fun n _ => logProb_nonneg hX n) _ x
      split_ifs with hx
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        field_simp [hx.ne']
      · have hPXeq : PX x = 0 := le_antisymm (not_lt.mp hx) hPX0
        refine Finset.sum_eq_zero fun y _ => ?_
        have hPXY0 : 0 ≤ PXY (x, y) := dist_nonneg _ _ (fun n _ => logProb_nonneg hX n) _ _
        have hle : PXY (x, y) ≤ ∑ y' : Ω, PXY (x, y') :=
          Finset.single_le_sum (fun y' _ => dist_nonneg _ _ (fun n _ => logProb_nonneg hX n) _ _)
            (Finset.mem_univ y)
        have hmarg : ∑ y' : Ω, PXY (x, y') = PX x := dist_prod_marg_fst _ _ XH YH x
        have : PXY (x, y) = 0 := by linarith
        rw [this, zero_mul]
    have hlin : ∀ t : ℝ, t * u ≤ D_H + t ^ 2 * V / 2 := by
      intro t
      rw [hu_group, Finset.mul_sum]
      have hsum_PX : ∑ x ∈ Finset.univ.filter (fun x : Fin H → Alph => 0 < PX x), PX x = 1 := by
        rw [Finset.sum_filter]
        trans ∑ x : Fin H → Alph, PX x
        · refine Finset.sum_congr rfl fun x _ => ?_
          have hPX0 : 0 ≤ PX x := dist_nonneg _ _ (fun n _ => logProb_nonneg hX n) _ x
          split_ifs with hx
          · rfl
          · exact (le_antisymm (not_lt.mp hx) hPX0).symm
        · exact sum_dist_eq_one _ _ (sum_logProb_eq_one hX) XH
      have hstep : ∑ x ∈ Finset.univ.filter (fun x : Fin H → Alph => 0 < PX x),
            t * (PX x * ∑ y : Ω, (PXY (x, y) / PX x) * proj (F x y)) ≤
          ∑ x ∈ Finset.univ.filter (fun x : Fin H → Alph => 0 < PX x),
            PX x * ((Real.log (Fintype.card Ω : ℝ) - shannonH (fun y : Ω => PXY (x, y) / PX x)) +
              t ^ 2 * V / 2) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hx_pos : 0 < PX x := (Finset.mem_filter.mp hx).2
        have hrew : t * (PX x * ∑ y : Ω, (PXY (x, y) / PX x) * proj (F x y)) =
            PX x * ∑ y : Ω, (PXY (x, y) / PX x) * (t * proj (F x y)) := by
          rw [mul_left_comm, Finset.mul_sum]
          congr 1; refine Finset.sum_congr rfl fun y _ => by ring
        rw [hrew]
        refine mul_le_mul_of_nonneg_left ?_ hx_pos.le
        have hPx0 : ∀ y : Ω, 0 ≤ PXY (x, y) / PX x := fun y =>
          div_nonneg (dist_nonneg _ _ (fun n _ => logProb_nonneg hX n) _ _) hx_pos.le
        have hPx1 : ∑ y : Ω, PXY (x, y) / PX x = 1 := by
          rw [← Finset.sum_div, dist_prod_marg_fst _ _ XH YH x, div_self hx_pos.ne']
        have hgibbs := gibbs_ineq (fun y : Ω => PXY (x, y) / PX x) hPx0 hPx1 (fun y => t * proj (F x y))
        have hmgf := hoeffding_product_mgf h H val hval hδ0 hδ14 hH proj hproj_le x t
        have hlog_mgf : Real.log ((1 / (Fintype.card Ω : ℝ)) * ∑ y : Ω, Real.exp (t * proj (F x y))) ≤
            t ^ 2 * V / 2 := by
          have hpos : 0 < (1 / (Fintype.card Ω : ℝ)) * ∑ y : Ω, Real.exp (t * proj (F x y)) :=
            mul_pos (one_div_pos.mpr (by exact_mod_cast Fintype.card_pos))
              (Finset.sum_pos (fun y _ => Real.exp_pos _) Finset.univ_nonempty)
          have h1 := Real.log_le_log hpos hmgf
          rwa [Real.log_exp] at h1
        linarith
      refine hstep.trans (le_of_eq ?_)
      have hcond := shannonH_cond_formula (logWindow X) (logProb X) (fun n _ => logProb_nonneg hX n) XH YH
      have hsplit : ∑ x ∈ Finset.univ.filter (fun x : Fin H → Alph => 0 < PX x),
            PX x * ((Real.log (Fintype.card Ω : ℝ) - shannonH (fun y : Ω => PXY (x, y) / PX x)) +
              t ^ 2 * V / 2) =
          (∑ x ∈ Finset.univ.filter (fun x : Fin H → Alph => 0 < PX x), PX x) *
            (Real.log (Fintype.card Ω : ℝ) + t ^ 2 * V / 2) -
          ∑ x ∈ Finset.univ.filter (fun x : Fin H → Alph => 0 < PX x),
            PX x * shannonH (fun y : Ω => PXY (x, y) / PX x) := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => by ring
      rw [hsplit, hsum_PX, one_mul, ← hcond]
      dsimp [D_H]; ring
    have hopt := hlin (u / V)
    have h1 : (u / V) * u = u ^ 2 / V := by ring
    have h2 : (u / V) ^ 2 * V / 2 = u ^ 2 / (2 * V) := by field_simp [hV_pos.ne']
    rw [h1, h2] at hopt
    have hdiff : u ^ 2 / V - u ^ 2 / (2 * V) = u ^ 2 / (2 * V) := by ring
    have h3 : u ^ 2 / (2 * V) ≤ D_H := by linarith
    have h4 := (div_le_iff₀ (by positivity : 0 < 2 * V)).mp h3
    linarith
  have hre : Z.re ^ 2 ≤ 2 * V * D_H := hproj_sq Complex.reLm Complex.abs_re_le_norm
  have him : Z.im ^ 2 ≤ 2 * V * D_H := hproj_sq Complex.imLm Complex.abs_im_le_norm
  have hnorm_sq : ‖Z‖ ^ 2 = Z.re ^ 2 + Z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  change ‖Z‖ ^ 2 ≤ 4 * V * D_H
  linarith

/- ### Section 6: Discretization, Scale Ladder, Entropy Decrement, and Main Proof -/

private noncomputable def gridVal (M : ℕ) (s : Fin (2 * M + 1) × Fin (2 * M + 1)) : ℂ :=
  ⟨(s.1.val : ℝ) / (M : ℝ) - 1, (s.2.val : ℝ) / (M : ℝ) - 1⟩

private noncomputable def quantizeCoord (M : ℕ) (t : ℝ) : Fin (2 * M + 1) :=
  ⟨min (2 * M) (Nat.floor ((M : ℝ) * (t + 1))), by omega⟩

private noncomputable def quantize (M : ℕ) (g : ℕ → ℂ) (n : ℕ) :
    Fin (2 * M + 1) × Fin (2 * M + 1) :=
  (quantizeCoord M (g n).re, quantizeCoord M (g n).im)

private lemma gridVal_norm_le_two {M : ℕ} (hM : 1 ≤ M) (s : Fin (2 * M + 1) × Fin (2 * M + 1)) :
    ‖gridVal M s‖ ≤ 2 := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcoord : ∀ a : Fin (2 * M + 1), |(a.val : ℝ) / (M : ℝ) - 1| ≤ 1 := by
    intro a
    have ha_le : (a.val : ℝ) ≤ 2 * (M : ℝ) := by
      have : a.val ≤ 2 * M := by omega
      exact_mod_cast this
    rw [abs_le]
    constructor
    · have : 0 ≤ (a.val : ℝ) / (M : ℝ) := by positivity
      linarith
    · have : (a.val : ℝ) / (M : ℝ) ≤ 2 := (div_le_iff₀ hM_pos).mpr (by linarith)
      linarith
  calc ‖gridVal M s‖ ≤ |(gridVal M s).re| + |(gridVal M s).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 + 1 := add_le_add (hcoord s.1) (hcoord s.2)
    _ = 2 := by norm_num

private lemma quantizeCoord_approx {M : ℕ} (hM : 1 ≤ M) {t : ℝ} (ht : |t| ≤ 1) :
    |t - (((quantizeCoord M t).val : ℝ) / (M : ℝ) - 1)| ≤ 1 / (M : ℝ) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have ht_bounds := abs_le.mp ht
  have hscaled_nn : 0 ≤ (M : ℝ) * (t + 1) := mul_nonneg hM_pos.le (by linarith)
  have hscaled_le : (M : ℝ) * (t + 1) ≤ (2 * M : ℕ) := by
    push_cast; nlinarith
  have hfl_le : Nat.floor ((M : ℝ) * (t + 1)) ≤ 2 * M := Nat.floor_le_of_le hscaled_le
  have hval : (quantizeCoord M t).val = Nat.floor ((M : ℝ) * (t + 1)) := by
    dsimp [quantizeCoord]
    exact min_eq_right hfl_le
  rw [hval]
  have hfl1 : (Nat.floor ((M : ℝ) * (t + 1)) : ℝ) ≤ (M : ℝ) * (t + 1) := Nat.floor_le hscaled_nn
  have hfl2 : (M : ℝ) * (t + 1) < (Nat.floor ((M : ℝ) * (t + 1)) : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [abs_le]
  constructor
  · have : (Nat.floor ((M : ℝ) * (t + 1)) : ℝ) / (M : ℝ) ≤ t + 1 :=
      (div_le_iff₀ hM_pos).mpr (by linarith)
    linarith [one_div_nonneg.mpr hM_pos.le]
  · have : t + 1 - (Nat.floor ((M : ℝ) * (t + 1)) : ℝ) / (M : ℝ) ≤ 1 / (M : ℝ) := by
      rw [le_div_iff₀ hM_pos]
      have hmul : (t + 1 - (Nat.floor ((M : ℝ) * (t + 1)) : ℝ) / (M : ℝ)) * (M : ℝ) =
          (M : ℝ) * (t + 1) - (Nat.floor ((M : ℝ) * (t + 1)) : ℝ) := by
        field_simp [hM_pos.ne']
      linarith
    linarith

private lemma quantize_approx {M : ℕ} (hM : 1 ≤ M) (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (n : ℕ) :
    ‖g n - gridVal M (quantize M g n)‖ ≤ 2 / (M : ℝ) := by
  have hre := quantizeCoord_approx hM ((Complex.abs_re_le_norm (g n)).trans (hg n))
  have him := quantizeCoord_approx hM ((Complex.abs_im_le_norm (g n)).trans (hg n))
  calc ‖g n - gridVal M (quantize M g n)‖
      ≤ |(g n - gridVal M (quantize M g n)).re| + |(g n - gridVal M (quantize M g n)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / (M : ℝ) + 1 / (M : ℝ) := add_le_add hre him
    _ = 2 / (M : ℝ) := by ring

private lemma discretization_error_bound (h H X M : ℕ) {δ η : ℝ}
    (hδ0 : 0 < δ) (hδ14 : δ ≤ 1 / 4) (hη0 : 0 < η)
    (hH : (16 / δ ^ 2 + 100 : ℝ) ≤ (H : ℝ)) (hX : 100 ≤ X)
    (hM2 : 2 ≤ M) (hMη : 216 / η ≤ (M : ℝ))
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) :
    let P := primeWindow δ H
    let f := quantize M g
    ‖((1 / (logWeightSum X : ℂ)) * ∑ n ∈ logWindow X, (1 / (n : ℂ)) *
        ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
              g (n + j) * star (g (n + j + p * h))
          else 0) -
      ((1 / (logWeightSum X : ℂ)) * ∑ n ∈ logWindow X, (1 / (n : ℂ)) *
        ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
              gridVal M (f (n + j)) * star (gridVal M (f (n + j + p * h)))
          else 0)‖ ≤ (η / 2) * (H : ℝ) / Real.log (H : ℝ) := by
  intro P f
  have hcheb := chebyshev_P_H_bounds hδ0 hδ14 hH
  have hlogH_pos : 0 < Real.log (H : ℝ) := by linarith [hcheb.1]
  have hL_pos : 0 < logWeightSum X := lt_of_lt_of_le zero_lt_one (logWeightSum_ge_one hX)
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hprod_diff : ∀ a b : ℕ,
      ‖g a * star (g b) - gridVal M (f a) * star (gridVal M (f b))‖ ≤ 6 / (M : ℝ) := by
    intro a b
    have hsplit : g a * star (g b) - gridVal M (f a) * star (gridVal M (f b)) =
        (g a - gridVal M (f a)) * star (g b) +
        gridVal M (f a) * star (g b - gridVal M (f b)) := by
      rw [star_sub]; ring
    rw [hsplit]
    calc ‖(g a - gridVal M (f a)) * star (g b) + gridVal M (f a) * star (g b - gridVal M (f b))‖
        ≤ ‖(g a - gridVal M (f a)) * star (g b)‖ + ‖gridVal M (f a) * star (g b - gridVal M (f b))‖ :=
          norm_add_le _ _
      _ = ‖g a - gridVal M (f a)‖ * ‖g b‖ + ‖gridVal M (f a)‖ * ‖g b - gridVal M (f b)‖ := by
          rw [norm_mul, norm_mul, norm_star, norm_star]
      _ ≤ (2 / (M : ℝ)) * 1 + 2 * (2 / (M : ℝ)) := by
          gcongr
          · exact quantize_approx (by omega) g hg a
          · exact hg b
          · exact gridVal_norm_le_two (by omega) (f a)
          · exact quantize_approx (by omega) g hg b
      _ = 6 / (M : ℝ) := by ring
  have hrew : ((1 / (logWeightSum X : ℂ)) * ∑ n ∈ logWindow X, (1 / (n : ℂ)) *
        ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
              g (n + j) * star (g (n + j + p * h))
          else 0) -
      ((1 / (logWeightSum X : ℂ)) * ∑ n ∈ logWindow X, (1 / (n : ℂ)) *
        ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
              gridVal M (f (n + j)) * star (gridVal M (f (n + j + p * h)))
          else 0) =
      ∑ n ∈ logWindow X, (logProb X n : ℂ) *
        ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
              (g (n + j) * star (g (n + j + p * h)) -
               gridVal M (f (n + j)) * star (gridVal M (f (n + j + p * h))))
          else 0 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp [logProb]; push_cast
    rw [← mul_sub, ← Finset.sum_sub_distrib, mul_assoc]
    congr 1; congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [hrew]
  have hpt_n : ∀ n ∈ logWindow X,
      ‖∑ p ∈ P, ∑ j ∈ Finset.Icc 1 H,
        if j + p * h ≤ H then
          ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
            (g (n + j) * star (g (n + j + p * h)) -
             gridVal M (f (n + j)) * star (gridVal M (f (n + j + p * h))))
        else 0‖ ≤ (η / 2) * (H : ℝ) / Real.log (H : ℝ) := by
    intro n _
    calc ‖∑ p ∈ P, ∑ j ∈ Finset.Icc 1 H, _‖
        ≤ ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 H,
            ‖if j + p * h ≤ H then
              ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
                (g (n + j) * star (g (n + j + p * h)) -
                 gridVal M (f (n + j)) * star (gridVal M (f (n + j + p * h))))
            else 0‖ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => norm_sum_le _ _)
      _ ≤ ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 H,
            ‖(if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)‖ * (6 / (M : ℝ)) := by
          refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hjp : j + p * h ≤ H
          · rw [if_pos hjp, norm_mul]
            exact mul_le_mul_of_nonneg_left (hprod_diff _ _) (norm_nonneg _)
          · rw [if_neg hjp, norm_zero]; positivity
      _ ≤ ∑ p ∈ P, (3 * (H : ℝ) / (p : ℝ)) * (6 / (M : ℝ)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [← Finset.sum_mul]
          have hp_mem := Finset.mem_filter.mp hp
          have hp_le_dH : (p : ℝ) ≤ δ * (H : ℝ) :=
            (by exact_mod_cast (Finset.mem_Icc.mp hp_mem.1).2 : (p : ℝ) ≤ (Nat.floor (δ * (H : ℝ)) : ℝ)).trans
              (Nat.floor_le (by positivity))
          have hp_le_H : p ≤ H := by
            have : (p : ℝ) ≤ (H : ℝ) := hp_le_dH.trans (by nlinarith)
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right
            (sum_abs_dvd_sub_inv_le n H p hp_mem.2.one_le hp_le_H) (by positivity)
      _ = (18 * (H : ℝ) / (M : ℝ)) * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ (18 * (H : ℝ) / (M : ℝ)) * (6 / Real.log (H : ℝ)) := by gcongr; exact hcheb.2.2.1
      _ = (108 / (M : ℝ)) * ((H : ℝ) / Real.log (H : ℝ)) := by ring
      _ ≤ (η / 2) * ((H : ℝ) / Real.log (H : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h1 : 216 ≤ (M : ℝ) * η := (div_le_iff₀ hη0).mp hMη
          rw [div_le_iff₀ hM_pos]; linarith
      _ = (η / 2) * (H : ℝ) / Real.log (H : ℝ) := by ring
  calc ‖∑ n ∈ logWindow X, (logProb X n : ℂ) * _‖
      ≤ ∑ n ∈ logWindow X, ‖(logProb X n : ℂ) * _‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ logWindow X, logProb X n * ((η / 2) * (H : ℝ) / Real.log (H : ℝ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logProb_nonneg hX n)]
        exact mul_le_mul_of_nonneg_left (hpt_n n hn) (logProb_nonneg hX n)
    _ = (η / 2) * (H : ℝ) / Real.log (H : ℝ) := by
        rw [← Finset.sum_mul, sum_logProb_eq_one hX, one_mul]

private noncomputable def scaleStep (c : ℝ) (H : ℕ) : ℕ :=
  Nat.ceil (2 * Real.log (H : ℝ) / c) + 2

private noncomputable def scaleSeq (c : ℝ) (H_start : ℕ) : ℕ → ℕ
  | 0 => H_start
  | r + 1 => scaleStep c (scaleSeq c H_start r) * scaleSeq c H_start r

private lemma scaleSeq_mono (c : ℝ) (H_start : ℕ) :
    Monotone (scaleSeq c H_start) := by
  refine monotone_nat_of_le_succ fun r => ?_
  dsimp [scaleSeq, scaleStep]
  have h2 : 1 ≤ Nat.ceil (2 * Real.log (scaleSeq c H_start r : ℝ) / c) + 2 := by omega
  calc scaleSeq c H_start r = 1 * scaleSeq c H_start r := (one_mul _).symm
    _ ≤ (Nat.ceil (2 * Real.log (scaleSeq c H_start r : ℝ) / c) + 2) * scaleSeq c H_start r :=
        Nat.mul_le_mul_right _ h2

private lemma scaleSeq_log_bound {c : ℝ} (hc : 0 < c) {H_start M₀ : ℕ}
    (hH_start : 100 ≤ H_start) (hM₀_H : H_start ≤ M₀)
    (hM₀_C : 4 * (2 / c + 3) ≤ (M₀ : ℝ)) :
    ∀ r : ℕ,
      Real.log (scaleSeq c H_start r : ℝ) ≤
        4 * ((r + M₀ : ℕ) : ℝ) * Real.log ((r + M₀ : ℕ) : ℝ) := by
  intro r
  have hM₀_ge100 : 100 ≤ M₀ := le_trans hH_start hM₀_H
  have hlog_ge1 : ∀ n : ℕ, 100 ≤ n → 1 ≤ Real.log (n : ℝ) := fun n hn => by
    have h1 : Real.exp 1 ≤ (n : ℝ) := by
      have : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  induction r with
  | zero =>
    simp only [Nat.zero_add, scaleSeq]
    have hlogH : Real.log (H_start : ℝ) ≤ (H_start : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by exact_mod_cast (show 0 < H_start by omega) : (0 : ℝ) < H_start)
      linarith
    have hlogM : 1 ≤ Real.log (M₀ : ℝ) := hlog_ge1 M₀ hM₀_ge100
    have hHM : (H_start : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀_H
    nlinarith
  | succ r ih =>
    set H := scaleSeq c H_start r
    set n := r + M₀
    have hH100 : 100 ≤ H := le_trans hH_start (scaleSeq_mono c H_start (Nat.zero_le r))
    have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
    have hlogH1 : 1 ≤ Real.log (H : ℝ) := hlog_ge1 H hH100
    have hlogH_pos : 0 < Real.log (H : ℝ) := by linarith
    have hn100 : 100 ≤ n := by omega
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hlogn1 : 1 ≤ Real.log (n : ℝ) := hlog_ge1 n hn100
    have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
    set C₀ : ℝ := 2 / c + 3
    have hC₀_pos : 0 < C₀ := by dsimp [C₀]; positivity
    have hk_le : (scaleStep c H : ℝ) ≤ C₀ * Real.log (H : ℝ) := by
      dsimp [scaleStep, C₀]
      have hceil : (Nat.ceil (2 * Real.log (H : ℝ) / c) : ℝ) < 2 * Real.log (H : ℝ) / c + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      push_cast
      have : 2 * Real.log (H : ℝ) / c = (2 / c) * Real.log (H : ℝ) := by ring
      nlinarith
    have hk_pos : (0 : ℝ) < (scaleStep c H : ℝ) := by dsimp [scaleStep]; positivity
    have hlog_next : Real.log (scaleSeq c H_start (r + 1) : ℝ) =
        Real.log (scaleStep c H : ℝ) + Real.log (H : ℝ) := by
      change Real.log (((scaleStep c H * H : ℕ) : ℝ)) = _
      rw [Nat.cast_mul, Real.log_mul hk_pos.ne' hH_pos.ne']
    have hlog_k : Real.log (scaleStep c H : ℝ) ≤ Real.log (4 * C₀) + Real.log (n : ℝ) + Real.log (Real.log (n : ℝ)) := by
      calc Real.log (scaleStep c H : ℝ)
          ≤ Real.log (C₀ * Real.log (H : ℝ)) := Real.log_le_log hk_pos hk_le
        _ ≤ Real.log (C₀ * (4 * (n : ℝ) * Real.log (n : ℝ))) :=
            Real.log_le_log (mul_pos hC₀_pos hlogH_pos) (mul_le_mul_of_nonneg_left ih hC₀_pos.le)
        _ = Real.log ((4 * C₀) * ((n : ℝ) * Real.log (n : ℝ))) := by congr 1; ring
        _ = Real.log (4 * C₀) + Real.log (n : ℝ) + Real.log (Real.log (n : ℝ)) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hn_pos.ne' hlogn_pos.ne']
            ring
    have hlog_4C : Real.log (4 * C₀) ≤ 2 * Real.log (n : ℝ) := by
      have hle : 4 * C₀ ≤ (n : ℝ) := hM₀_C.trans (by exact_mod_cast (show M₀ ≤ n by omega))
      have h1 := Real.log_le_log (by positivity) hle
      linarith
    have hlog_log : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
      have hle : Real.log (n : ℝ) ≤ (n : ℝ) := by
        have := Real.log_le_sub_one_of_pos hn_pos; linarith
      exact Real.log_le_log hlogn_pos hle
    have hlog_mono : Real.log (n : ℝ) ≤ Real.log ((r + 1 + M₀ : ℕ) : ℝ) :=
      Real.log_le_log hn_pos (by exact_mod_cast (show n ≤ r + 1 + M₀ by omega))
    have hcast : ((r + 1 + M₀ : ℕ) : ℝ) = (n : ℝ) + 1 := by
      have : r + 1 + M₀ = n + 1 := by omega
      rw [this]; push_cast; ring
    rw [hcast] at hlog_mono ⊢
    calc Real.log (scaleSeq c H_start (r + 1) : ℝ)
        = Real.log (scaleStep c H : ℝ) + Real.log (H : ℝ) := hlog_next
      _ ≤ (2 * Real.log (n : ℝ) + Real.log (n : ℝ) + Real.log (n : ℝ)) +
          4 * (n : ℝ) * Real.log (n : ℝ) := by linarith [hlog_k, hlog_4C, hlog_log, ih]
      _ = 4 * ((n : ℝ) + 1) * Real.log (n : ℝ) := by ring
      _ ≤ 4 * ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) := by gcongr

private lemma sum_inv_n_log_n_ge {M₀ : ℕ} (hM₀ : 16 ≤ M₀) (R : ℕ) :
    Real.log (Real.log ((R + M₀ : ℕ) : ℝ)) - Real.log (Real.log (M₀ : ℝ)) ≤
      ∑ r ∈ Finset.range R, (1 : ℝ) / (((r + M₀ : ℕ) : ℝ) * Real.log ((r + M₀ : ℕ) : ℝ)) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ]
    set n := R + M₀
    have hn16 : 16 ≤ n := by omega
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hlogn1 : 1 ≤ Real.log (n : ℝ) := by
      have h1 : Real.exp 1 ≤ (n : ℝ) := by
        have : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn16
        linarith [Real.exp_one_lt_d9]
      have := Real.log_le_log (Real.exp_pos 1) h1
      rwa [Real.log_exp] at this
    have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
    have hlogn1_pos : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le hlogn_pos (Real.log_le_log hn_pos (by exact_mod_cast Nat.le_succ n))
    have hstep : Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ)) ≤
        1 / ((n : ℝ) * Real.log (n : ℝ)) := by
      rw [← Real.log_div hlogn1_pos.ne' hlogn_pos.ne']
      calc Real.log (Real.log ((n + 1 : ℕ) : ℝ) / Real.log (n : ℝ))
          ≤ Real.log ((n + 1 : ℕ) : ℝ) / Real.log (n : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (div_pos hlogn1_pos hlogn_pos)
        _ = (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) / Real.log (n : ℝ) := by
            field_simp [hlogn_pos.ne']
        _ = Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) / Real.log (n : ℝ) := by
            rw [Real.log_div hn1_pos.ne' hn_pos.ne']
        _ ≤ (((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1) / Real.log (n : ℝ) :=
            div_le_div_of_nonneg_right (Real.log_le_sub_one_of_pos (div_pos hn1_pos hn_pos)) hlogn_pos.le
        _ = 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
            push_cast; field_simp [hn_pos.ne', hlogn_pos.ne']; ring
    have heq : R + 1 + M₀ = n + 1 := by omega
    rw [heq]
    linarith

private def block_split_equiv (k H : ℕ) (hH : 0 < H) (Alph : Type*) :
    (Fin (k * H) → Alph) ≃ (Fin k → Fin H → Alph) :=
  { toFun := fun x m j => x ⟨m.val * H + j.val, by
      have hm := m.isLt; have hj := j.isLt
      calc m.val * H + j.val < m.val * H + H := by omega
        _ = (m.val + 1) * H := by ring
        _ ≤ k * H := Nat.mul_le_mul_right H hm⟩
    invFun := fun b i => b ⟨i.val / H, (Nat.div_lt_iff_lt_mul hH).mpr i.isLt⟩
      ⟨i.val % H, Nat.mod_lt i.val hH⟩
    left_inv := fun x => by
      funext i
      dsimp only
      congr 1
      apply Fin.ext
      dsimp
      have := Nat.div_add_mod i.val H
      linarith [mul_comm H (i.val / H)]
    right_inv := fun b => by
      funext m j
      dsimp only
      have hdiv : (m.val * H + j.val) / H = m.val := by
        rw [Nat.mul_comm, Nat.mul_add_div hH, Nat.div_eq_of_lt j.isLt, add_zero]
      have hmod : (m.val * H + j.val) % H = j.val := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
      have hm_eq : (⟨(m.val * H + j.val) / H, (Nat.div_lt_iff_lt_mul hH).mpr (by
        have hm := m.isLt; have hj := j.isLt
        calc m.val * H + j.val < m.val * H + H := by omega
          _ = (m.val + 1) * H := by ring
          _ ≤ k * H := Nat.mul_le_mul_right H hm)⟩ : Fin k) = m := Fin.ext hdiv
      have hj_eq : (⟨(m.val * H + j.val) % H, Nat.mod_lt _ hH⟩ : Fin H) = j := Fin.ext hmod
      rw [hm_eq, hj_eq] }

private lemma entropy_decrement_step {c δ : ℝ} {H k X U_max : ℕ}
    {Alph : Type*} [Fintype Alph] [Nonempty Alph]
    (hc : 0 < c) (hδ0 : 0 < δ) (hδ14 : δ ≤ 1 / 4)
    (hH : (16 / δ ^ 2 + 100 : ℝ) ≤ (H : ℝ))
    (hk : k = scaleStep c H) (hX : 100 ≤ X)
    [∀ p : primeWindow δ H, NeZero p.1]
    (hU_prod : (Fintype.card Alph) ^ H * (∏ p ∈ primeWindow δ H, p) ≤ U_max)
    (hU_kH : k * H ≤ U_max)
    (hU_Q : ∏ p ∈ primeWindow δ H, p ≤ U_max)
    (hU_sq : U_max ≤ Nat.sqrt X)
    (herr : 4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ)) ≤
      c / (4 * Real.log (H : ℝ)))
    (f : ℕ → Alph) :
    let P := primeWindow δ H
    let Ω := ∀ p : P, ZMod p.1
    let XH : ℕ → (Fin H → Alph) := blockOf H f
    let YH : ℕ → Ω := fun n p => (n : ZMod p.1)
    let D_H : ℝ := Real.log (Fintype.card Ω : ℝ) -
      (shannonH (dist (logWindow X) (logProb X) (fun n => (XH n, YH n))) -
       shannonH (dist (logWindow X) (logProb X) XH))
    shannonH (dist (logWindow X) (logProb X) (blockOf (k * H) f)) / ((k * H : ℕ) : ℝ) ≤
      shannonH (dist (logWindow X) (logProb X) XH) / (H : ℝ) -
      D_H / (H : ℝ) + (3 * c / 4) / Real.log (H : ℝ) := by
  intro P Ω XH YH D_H
  have hcheb := chebyshev_P_H_bounds hδ0 hδ14 hH
  have hH100 : 100 ≤ H := by
    have : (100 : ℝ) ≤ (H : ℝ) := by
      have : 0 < 16 / δ ^ 2 := by positivity
      linarith
    exact_mod_cast this
  have hH_pos : 0 < H := by omega
  have hH_r : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
  have hk_ge2 : 2 ≤ k := by rw [hk]; dsimp [scaleStep]; omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hlogH_pos : 0 < Real.log (H : ℝ) := by linarith [hcheb.1]
  have hcardΩ : Fintype.card Ω = ∏ p ∈ P, p := by
    dsimp [Ω]
    rw [Fintype.card_pi]
    calc ∏ p : P, Fintype.card (ZMod p.1)
        = ∏ p : P, p.1 := Finset.prod_congr rfl fun p _ => ZMod.card p.1
      _ = ∏ p ∈ P, p := Finset.prod_coe_sort P (fun p => p)
  have hP_prime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hlogΩ_le_H : Real.log (Fintype.card Ω : ℝ) ≤ (H : ℝ) := by
    rw [hcardΩ]; exact hcheb.2.1
  have hHY_le_H : shannonH (dist (logWindow X) (logProb X) YH) ≤ (H : ℝ) :=
    (shannonH_le_log_card _
      (fun y => dist_nonneg _ _ (fun n _ => logProb_nonneg hX n) _ y)
      (sum_dist_eq_one _ _ (sum_logProb_eq_one hX) YH)).trans hlogΩ_le_H
  have hunif := shannonH_Y_near_uniform P hX hP_prime (hU_Q.trans hU_sq)
  have hunif_err : Real.log (Fintype.card Ω : ℝ) - shannonH (dist (logWindow X) (logProb X) YH) ≤
      (U_max : ℝ) * (2 * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))) := by
    rw [hcardΩ]
    have h1 := (abs_le.mp hunif).1
    have h2 : ((∏ p ∈ P, p : ℕ) : ℝ) * (2 * Real.sqrt (3 * ((∏ p ∈ P, p : ℕ) : ℝ) / (Nat.sqrt X : ℝ))) ≤
        (U_max : ℝ) * (2 * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))) := by
      gcongr
    linarith
  let B : Fin k → ℕ → (Fin H → Alph) := fun m n => XH (n + m.val * H)
  have hsplit_eq : shannonH (dist (logWindow X) (logProb X) (fun n => (YH n, blockOf (k * H) f n))) =
      shannonH (dist (logWindow X) (logProb X) (fun n => (YH n, fun m : Fin k => B m n))) := by
    let e := Equiv.prodCongr (Equiv.refl Ω) (block_split_equiv k H hH_pos Alph)
    have hcomp : (fun n => (YH n, fun m : Fin k => B m n)) =
        e ∘ (fun n => (YH n, blockOf (k * H) f n)) := by
      funext n
      refine Prod.ext rfl (funext fun m => funext fun j => ?_)
      simp only [Function.comp_apply, e, block_split_equiv, B, XH, blockOf,
        Equiv.prodCongr_apply, Equiv.coe_fn_mk, Prod.map_apply]
      congr 1; omega
    rw [hcomp, shannonH_equiv]
  have hmono : shannonH (dist (logWindow X) (logProb X) (blockOf (k * H) f)) ≤
      shannonH (dist (logWindow X) (logProb X) (fun n => (YH n, blockOf (k * H) f n))) := by
    have h1 := shannonH_mono (logWindow X) (logProb X) (fun n _ => logProb_nonneg hX n)
      (blockOf (k * H) f) YH
    have hswap : shannonH (dist (logWindow X) (logProb X) (fun n => (YH n, blockOf (k * H) f n))) =
        shannonH (dist (logWindow X) (logProb X) (fun n => (blockOf (k * H) f n, YH n))) := by
      have hcomp : (fun n => (YH n, blockOf (k * H) f n)) =
          (Equiv.prodComm (Fin (k * H) → Alph) Ω) ∘ (fun n => (blockOf (k * H) f n, YH n)) := rfl
      rw [hcomp]
      exact shannonH_equiv (logWindow X) (logProb X) (fun n => (blockOf (k * H) f n, YH n))
        (Equiv.prodComm (Fin (k * H) → Alph) Ω)
    linarith only [h1, hswap]
  have hsub := shannonH_cond_fin_subadd (logWindow X) (logProb X)
    (fun n _ => logProb_nonneg hX n) YH k B
  have hterm_m : ∀ m : Fin k,
      shannonH (dist (logWindow X) (logProb X) (fun n => (YH n, B m n))) -
        shannonH (dist (logWindow X) (logProb X) YH) ≤
      shannonH (dist (logWindow X) (logProb X) XH) - D_H +
        4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ)) := by
    intro m
    set s : ℕ := m.val * H
    have hs_le_U : s ≤ U_max := by
      have : m.val * H ≤ k * H := Nat.mul_le_mul_right H (le_of_lt m.isLt)
      exact this.trans hU_kH
    have hs_le_sq : s ≤ Nat.sqrt X := hs_le_U.trans hU_sq
    let e_sh : Ω ≃ Ω :=
      { toFun := fun y p => y p + (s : ZMod p.1)
        invFun := fun y p => y p - (s : ZMod p.1)
        left_inv := fun y => funext fun p => add_sub_cancel_right _ _
        right_inv := fun y => funext fun p => sub_add_cancel _ _ }
    let e_full : Ω × (Fin H → Alph) ≃ (Fin H → Alph) × Ω :=
      (Equiv.prodCongr e_sh (Equiv.refl _)).trans (Equiv.prodComm _ _)
    have hcomp_m : (fun n => (XH (n + s), YH (n + s))) = e_full ∘ (fun n => (YH n, B m n)) := by
      funext n
      refine Prod.ext rfl (funext fun p => ?_)
      simp only [Function.comp_apply, e_full, e_sh, YH, Equiv.trans_apply, Equiv.prodCongr_apply,
        Equiv.prodComm_apply, Equiv.coe_fn_mk, Prod.map_apply, Prod.swap_prod_mk, Nat.cast_add]
    have hshift_eq : shannonH (dist (logWindow X) (logProb X) (fun n => (YH n, B m n))) =
        shannonH (dist (logWindow X) (logProb X) (fun n => (XH (n + s), YH (n + s)))) := by
      rw [hcomp_m, shannonH_equiv]
    rw [hshift_eq]
    have hsh_bd := shannonH_shift_abs_le hX hs_le_sq (fun n => (XH n, YH n))
    have hcard_prod : Fintype.card ((Fin H → Alph) × Ω) ≤ U_max := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hcardΩ]
      exact hU_prod
    have hsh_err : shannonH (dist (logWindow X) (logProb X) (fun n => (XH (n + s), YH (n + s)))) -
        shannonH (dist (logWindow X) (logProb X) (fun n => (XH n, YH n))) ≤
        (U_max : ℝ) * (2 * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))) := by
      have h1 := (abs_le.mp hsh_bd).2
      have h2 : (Fintype.card ((Fin H → Alph) × Ω) : ℝ) * (2 * Real.sqrt (3 * (s : ℝ) / (Nat.sqrt X : ℝ))) ≤
          (U_max : ℝ) * (2 * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))) := by
        gcongr
      linarith
    dsimp [D_H]
    linarith
  have htot : shannonH (dist (logWindow X) (logProb X) (blockOf (k * H) f)) ≤
      (H : ℝ) + (k : ℝ) * (shannonH (dist (logWindow X) (logProb X) XH) - D_H +
        4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))) := by
    have hsum_le : ∑ m : Fin k,
        (shannonH (dist (logWindow X) (logProb X) (fun n => (YH n, B m n))) -
          shannonH (dist (logWindow X) (logProb X) YH)) ≤
        (k : ℝ) * (shannonH (dist (logWindow X) (logProb X) XH) - D_H +
          4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))) := by
      calc _ ≤ ∑ _m : Fin k, (shannonH (dist (logWindow X) (logProb X) XH) - D_H +
              4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))) :=
            Finset.sum_le_sum fun m _ => hterm_m m
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hkH_pos : (0 : ℝ) < ((k * H : ℕ) : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right htot hkH_pos.le
  have hinv_k : 1 / (k : ℝ) ≤ c / (2 * Real.log (H : ℝ)) := by
    have h2 : 2 * Real.log (H : ℝ) / c ≤ (k : ℝ) := by
      rw [hk]; dsimp [scaleStep]; push_cast
      linarith [Nat.le_ceil (2 * Real.log (H : ℝ) / c)]
    have h1 := one_div_le_one_div_of_le (by positivity) h2
    rwa [one_div_div] at h1
  have herr_div : (4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))) / (H : ℝ) ≤
      c / (4 * Real.log (H : ℝ)) := by
    have h1leH : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast (show 1 ≤ H by omega)
    calc (4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))) / (H : ℝ)
        ≤ (4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))) / 1 :=
          div_le_div_of_nonneg_left (by positivity) zero_lt_one h1leH
      _ = 4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ)) := div_one _
      _ ≤ c / (4 * Real.log (H : ℝ)) := herr
  have hrew : ((H : ℝ) + (k : ℝ) * (shannonH (dist (logWindow X) (logProb X) XH) - D_H +
      4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ)))) / ((k * H : ℕ) : ℝ) =
      1 / (k : ℝ) + shannonH (dist (logWindow X) (logProb X) XH) / (H : ℝ) - D_H / (H : ℝ) +
      (4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))) / (H : ℝ) := by
    push_cast; field_simp [hk_pos.ne', hH_r.ne']; ring
  rw [hrew] at hdiv
  have h34 : (3 * c / 4) / Real.log (H : ℝ) = c / (2 * Real.log (H : ℝ)) + c / (4 * Real.log (H : ℝ)) := by
    field_simp [hlogH_pos.ne']; ring
  linarith

private lemma combine_good_scale (h H X M : ℕ) {δ η : ℝ}
    (hδ0 : 0 < δ) (hδ14 : δ ≤ 1 / 4) (hη0 : 0 < η)
    (hH : (16 / δ ^ 2 + 100 : ℝ) ≤ (H : ℝ)) (hX : 100 ≤ X)
    (hM2 : 2 ≤ M) (hMη : 216 / η ≤ (M : ℝ))
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    [∀ p : primeWindow δ H, NeZero p.1]
    (hgood :
      let P := primeWindow δ H
      let Ω := ∀ p : P, ZMod p.1
      let XH := blockOf H (quantize M g)
      let YH : ℕ → Ω := fun n p => (n : ZMod p.1)
      Real.log (Fintype.card Ω : ℝ) -
        (shannonH (dist (logWindow X) (logProb X) (fun n => (XH n, YH n))) -
         shannonH (dist (logWindow X) (logProb X) XH)) ≤
        (δ * η ^ 2 / 30000) * (H : ℝ) / Real.log (H : ℝ)) :
    ‖(1 / (logWeightSum X : ℂ)) * ∑ n ∈ logWindow X, (1 / (n : ℂ)) *
      ∑ p ∈ primeWindow δ H, ∑ j ∈ Finset.Icc 1 H,
        if j + p * h ≤ H then
          ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
            g (n + j) * star (g (n + j + p * h))
        else 0‖ ≤ η * (H : ℝ) / Real.log (H : ℝ) := by
  have hlogH_pos : 0 < Real.log (H : ℝ) :=
    lt_of_lt_of_le zero_lt_one (chebyshev_P_H_bounds hδ0 hδ14 hH).1
  have hdisc := discretization_error_bound h H X M hδ0 hδ14 hη0 hH hX hM2 hMη g hg
  have hdec_sq := bilinear_decoupling_bound h H X (gridVal M)
    (gridVal_norm_le_two (by omega)) (quantize M g) hδ0 hδ14 hH hX
  have hdec_le : ‖(1 / (logWeightSum X : ℂ)) * ∑ n ∈ logWindow X, (1 / (n : ℂ)) *
      ∑ p ∈ primeWindow δ H, ∑ j ∈ Finset.Icc 1 H,
        if j + p * h ≤ H then
          ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
            gridVal M (quantize M g (n + j)) * star (gridVal M (quantize M g (n + j + p * h)))
        else 0‖ ≤ (η / 2) * (H : ℝ) / Real.log (H : ℝ) := by
    set V := 1728 * (H : ℝ) / (δ * Real.log (H : ℝ))
    have h4VD : 4 * V * ((δ * η ^ 2 / 30000) * (H : ℝ) / Real.log (H : ℝ)) ≤
        ((η / 2) * (H : ℝ) / Real.log (H : ℝ)) ^ 2 := by
      dsimp [V]
      have hrew : 4 * (1728 * (H : ℝ) / (δ * Real.log (H : ℝ))) *
          ((δ * η ^ 2 / 30000) * (H : ℝ) / Real.log (H : ℝ)) =
          (6912 / 30000) * (η * (H : ℝ) / Real.log (H : ℝ)) ^ 2 := by
        field_simp [hδ0.ne', hlogH_pos.ne']; ring
      have hrew2 : ((η / 2) * (H : ℝ) / Real.log (H : ℝ)) ^ 2 =
          (1 / 4) * (η * (H : ℝ) / Real.log (H : ℝ)) ^ 2 := by ring
      rw [hrew, hrew2]
      exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
    have hsq_le : ‖(1 / (logWeightSum X : ℂ)) * ∑ n ∈ logWindow X, (1 / (n : ℂ)) *
        ∑ p ∈ primeWindow δ H, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
              gridVal M (quantize M g (n + j)) * star (gridVal M (quantize M g (n + j + p * h)))
          else 0‖ ^ 2 ≤ ((η / 2) * (H : ℝ) / Real.log (H : ℝ)) ^ 2 :=
      hdec_sq.trans ((mul_le_mul_of_nonneg_left hgood (by dsimp [V]; positivity)).trans h4VD)
    exact le_of_sq_le_sq hsq_le (div_nonneg (mul_nonneg (div_nonneg hη0.le (by norm_num))
      (Nat.cast_nonneg H)) hlogH_pos.le)
  have htri := norm_add_le
    (((1 / (logWeightSum X : ℂ)) * ∑ n ∈ logWindow X, (1 / (n : ℂ)) *
        ∑ p ∈ primeWindow δ H, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
              g (n + j) * star (g (n + j + p * h))
          else 0) -
      ((1 / (logWeightSum X : ℂ)) * ∑ n ∈ logWindow X, (1 / (n : ℂ)) *
        ∑ p ∈ primeWindow δ H, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
              gridVal M (quantize M g (n + j)) * star (gridVal M (quantize M g (n + j + p * h)))
          else 0))
    ((1 / (logWeightSum X : ℂ)) * ∑ n ∈ logWindow X, (1 / (n : ℂ)) *
      ∑ p ∈ primeWindow δ H, ∑ j ∈ Finset.Icc 1 H,
        if j + p * h ≤ H then
          ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
            gridVal M (quantize M g (n + j)) * star (gridVal M (quantize M g (n + j + p * h)))
        else 0)
  rw [sub_add_cancel] at htri
  have hhalf : (η / 2) * (H : ℝ) / Real.log (H : ℝ) + (η / 2) * (H : ℝ) / Real.log (H : ℝ) =
      η * (H : ℝ) / Real.log (H : ℝ) := by ring
  linarith only [htri, hdisc, hdec_le, hhalf]

end Erdos67H2

theorem OMA.solution : OMA.R_Erdos67_erdos_67_R1_H1_R1.H2 := by
  intro h hh δ η hδ0 hδ14 hη0 H₀ hH₀
  set M : ℕ := Nat.ceil (216 / η) + 2
  have hM2 : 2 ≤ M := by omega
  have hMη : 216 / η ≤ (M : ℝ) := by
    dsimp [M]; push_cast; linarith [Nat.le_ceil (216 / η)]
  let Alph := Fin (2 * M + 1) × Fin (2 * M + 1)
  have hcardAlph_pos : (0 : ℝ) < (Fintype.card Alph : ℝ) := by exact_mod_cast Fintype.card_pos
  set c : ℝ := δ * η ^ 2 / 30000
  have hc : 0 < c := by positivity
  set H_start : ℕ := max H₀ (Nat.ceil (16 / δ ^ 2) + 100)
  have hH₀_le_start : H₀ ≤ H_start := le_max_left _ _
  have hH_start_ge : (16 / δ ^ 2 + 100 : ℝ) ≤ (H_start : ℝ) := by
    have h1 : (Nat.ceil (16 / δ ^ 2) + 100 : ℕ) ≤ H_start := le_max_right _ _
    have h2 : ((Nat.ceil (16 / δ ^ 2) + 100 : ℕ) : ℝ) ≤ (H_start : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith [Nat.le_ceil (16 / δ ^ 2)]
  have hH_start_100 : 100 ≤ H_start := by
    have : (100 : ℝ) ≤ (H_start : ℝ) := by
      have : 0 < 16 / δ ^ 2 := by positivity
      linarith
    exact_mod_cast this
  set M₀ : ℕ := max H_start (Nat.ceil (4 * (2 / c + 3)) + 16)
  have hM₀_H : H_start ≤ M₀ := le_max_left _ _
  have hM₀_16 : 16 ≤ M₀ := le_trans (by omega : 16 ≤ Nat.ceil (4 * (2 / c + 3)) + 16) (le_max_right _ _)
  have hM₀_C : 4 * (2 / c + 3) ≤ (M₀ : ℝ) := by
    have h1 : (Nat.ceil (4 * (2 / c + 3)) + 16 : ℕ) ≤ M₀ := le_max_right _ _
    have h2 : ((Nat.ceil (4 * (2 / c + 3)) + 16 : ℕ) : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith [Nat.le_ceil (4 * (2 / c + 3))]
  set R : ℕ := Nat.ceil (Real.exp (Real.exp (Real.log (Real.log (M₀ : ℝ)) +
      16 * Real.log (Fintype.card Alph : ℝ) / c + 2))) + 1
  have hR_pos : 1 ≤ R := by omega
  set H₁ : ℕ := Erdos67H2.scaleSeq c H_start R
  have hH_start_le_H₁ : H_start ≤ H₁ := Erdos67H2.scaleSeq_mono c H_start (Nat.zero_le R)
  have hH₀_le_H₁ : H₀ ≤ H₁ := le_trans hH₀_le_start hH_start_le_H₁
  have hH₁_ge : (16 / δ ^ 2 + 100 : ℝ) ≤ (H₁ : ℝ) :=
    hH_start_ge.trans (by exact_mod_cast hH_start_le_H₁)
  have hlogH₁_ge1 : 1 ≤ Real.log (H₁ : ℝ) :=
    (Erdos67H2.chebyshev_P_H_bounds hδ0 hδ14 hH₁_ge).1
  have hlogH₁_pos : 0 < Real.log (H₁ : ℝ) := by linarith
  set Q_all : ℕ := ∏ p ∈ (Finset.Icc 1 H₁).filter Nat.Prime, p
  set U_max : ℕ := (Fintype.card Alph) ^ H₁ * Q_all + H₁ + 1
  have hU_max_pos : 1 ≤ U_max := by omega
  set K_A : ℕ := max (max 10 U_max)
    (Nat.ceil (3 * (U_max : ℝ) * (16 * (U_max : ℝ) * Real.log (H₁ : ℝ) / c + 1) ^ 2) + 1)
  set A : ℝ := ((K_A ^ 2 : ℕ) : ℝ)
  have hA_ge1 : 1 ≤ A := by
    have h10 : 10 ≤ K_A := le_trans (le_max_left 10 U_max) (le_max_left _ _)
    have : 1 ≤ K_A ^ 2 := by nlinarith
    dsimp only [A]
    exact_mod_cast this
  refine ⟨H₁, A, hH₀_le_H₁, hA_ge1, fun X hX g hg => ?_⟩
  have hKA_sq_le_X : K_A ^ 2 ≤ X := by
    dsimp only [A] at hX
    exact_mod_cast hX
  have hKA_le_sq : K_A ≤ Nat.sqrt X := by
    refine Nat.le_sqrt.mpr ?_
    rw [← sq]
    exact hKA_sq_le_X
  have hX100 : 100 ≤ X := by
    have h10 : 10 ≤ K_A := le_trans (le_max_left 10 U_max) (le_max_left _ _)
    nlinarith
  have hU_le_sq : U_max ≤ Nat.sqrt X :=
    le_trans (le_trans (le_max_right 10 U_max) (le_max_left _ _)) hKA_le_sq
  have herr_all : 4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ)) ≤
      c / (4 * Real.log (H₁ : ℝ)) := by
    have hsq_pos : (0 : ℝ) < (Nat.sqrt X : ℝ) := by
      have : 10 ≤ Nat.sqrt X := le_trans (le_trans (le_max_left 10 U_max) (le_max_left _ _)) hKA_le_sq
      exact_mod_cast (show 0 < Nat.sqrt X by omega)
    have hsq_ge : 3 * (U_max : ℝ) * (16 * (U_max : ℝ) * Real.log (H₁ : ℝ) / c + 1) ^ 2 ≤ (Nat.sqrt X : ℝ) := by
      have h1 : Nat.ceil (3 * (U_max : ℝ) * (16 * (U_max : ℝ) * Real.log (H₁ : ℝ) / c + 1) ^ 2) + 1 ≤ K_A :=
        le_max_right _ _
      have h2 : ((Nat.ceil (3 * (U_max : ℝ) * (16 * (U_max : ℝ) * Real.log (H₁ : ℝ) / c + 1) ^ 2) + 1 : ℕ) : ℝ) ≤
          (Nat.sqrt X : ℝ) := by exact_mod_cast h1.trans hKA_le_sq
      push_cast at h2
      linarith [Nat.le_ceil (3 * (U_max : ℝ) * (16 * (U_max : ℝ) * Real.log (H₁ : ℝ) / c + 1) ^ 2)]
    have hden_pos : 0 < 16 * (U_max : ℝ) * Real.log (H₁ : ℝ) / c + 1 := by positivity
    have hdiv_le : 3 * (U_max : ℝ) / (Nat.sqrt X : ℝ) ≤
        (1 / (16 * (U_max : ℝ) * Real.log (H₁ : ℝ) / c + 1)) ^ 2 := by
      rw [div_pow, one_pow, div_le_div_iff₀ hsq_pos (by positivity)]
      linarith
    have hrt : Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ)) ≤
        1 / (16 * (U_max : ℝ) * Real.log (H₁ : ℝ) / c + 1) := by
      calc Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))
          ≤ Real.sqrt ((1 / (16 * (U_max : ℝ) * Real.log (H₁ : ℝ) / c + 1)) ^ 2) :=
            Real.sqrt_le_sqrt hdiv_le
        _ = 1 / (16 * (U_max : ℝ) * Real.log (H₁ : ℝ) / c + 1) :=
            Real.sqrt_sq (by positivity)
    calc 4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ))
        ≤ 4 * (U_max : ℝ) * (1 / (16 * (U_max : ℝ) * Real.log (H₁ : ℝ) / c + 1)) := by gcongr
      _ ≤ 4 * (U_max : ℝ) * (1 / (16 * (U_max : ℝ) * Real.log (H₁ : ℝ) / c)) := by
          gcongr
          linarith only []
      _ = c / (4 * Real.log (H₁ : ℝ)) := by
          have hU_r : (0 : ℝ) < (U_max : ℝ) := by exact_mod_cast hU_max_pos
          field_simp [hU_r.ne', hlogH₁_pos.ne', hc.ne']
          ring
  let f : ℕ → Alph := Erdos67H2.quantize M g
  -- Pigeonhole over r ∈ Finset.range R to find a good scale H = scaleSeq c H_start r
  have hexists_r : ∃ r ∈ Finset.range R,
      let Hr := Erdos67H2.scaleSeq c H_start r
      let Pr := Erdos67H2.primeWindow δ Hr
      haveI : ∀ p : Pr, NeZero p.1 := fun p => ⟨(Finset.mem_filter.mp p.2).2.ne_zero⟩
      let Ωr := ∀ p : Pr, ZMod p.1
      let XHr := Erdos67H2.blockOf Hr f
      let YHr : ℕ → Ωr := fun n p => (n : ZMod p.1)
      Real.log (Fintype.card Ωr : ℝ) -
        (Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X) (fun n => (XHr n, YHr n))) -
         Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X) XHr)) ≤
        c * (Hr : ℝ) / Real.log (Hr : ℝ) := by
    by_contra hall
    push Not at hall
    have hstep_r : ∀ r ∈ Finset.range R,
        (c / 4) / Real.log (Erdos67H2.scaleSeq c H_start r : ℝ) <
          Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
            (Erdos67H2.blockOf (Erdos67H2.scaleSeq c H_start r) f)) / (Erdos67H2.scaleSeq c H_start r : ℝ) -
          Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
            (Erdos67H2.blockOf (Erdos67H2.scaleSeq c H_start (r + 1)) f)) /
            (Erdos67H2.scaleSeq c H_start (r + 1) : ℝ) := by
      intro r hr
      have hr_lt : r < R := Finset.mem_range.mp hr
      set Hr := Erdos67H2.scaleSeq c H_start r
      set kr := Erdos67H2.scaleStep c Hr
      have hHr_ge : (16 / δ ^ 2 + 100 : ℝ) ≤ (Hr : ℝ) :=
        hH_start_ge.trans (by exact_mod_cast Erdos67H2.scaleSeq_mono c H_start (Nat.zero_le r))
      have hHr_le_H₁ : Hr ≤ H₁ := Erdos67H2.scaleSeq_mono c H_start (le_of_lt hr_lt)
      have hHr1_le_H₁ : kr * Hr ≤ H₁ := Erdos67H2.scaleSeq_mono c H_start hr_lt
      have hHr_pos : (0 : ℝ) < (Hr : ℝ) := by
        have : 0 < 16 / δ ^ 2 := by positivity
        linarith
      have hlogHr_pos : 0 < Real.log (Hr : ℝ) := by
        linarith [(Erdos67H2.chebyshev_P_H_bounds hδ0 hδ14 hHr_ge).1]
      have hPr_sub : Erdos67H2.primeWindow δ Hr ⊆ (Finset.Icc 1 H₁).filter Nat.Prime := by
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hp_le_dH : (p : ℝ) ≤ δ * (Hr : ℝ) :=
          (by exact_mod_cast (Finset.mem_Icc.mp hp'.1).2 : (p : ℝ) ≤ (Nat.floor (δ * (Hr : ℝ)) : ℝ)).trans
            (Nat.floor_le (by positivity))
        have hp_le_H₁ : p ≤ H₁ := by
          have : (p : ℝ) ≤ (Hr : ℝ) := hp_le_dH.trans (by nlinarith)
          exact le_trans (by exact_mod_cast this) hHr_le_H₁
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp'.2.one_le, hp_le_H₁⟩, hp'.2⟩
      have hQr_le : ∏ p ∈ Erdos67H2.primeWindow δ Hr, p ≤ Q_all :=
        Finset.prod_le_prod_of_subset_of_one_le' hPr_sub fun p hp _ => (Finset.mem_filter.mp hp).2.one_le
      have hU_prod : (Fintype.card Alph) ^ Hr * (∏ p ∈ Erdos67H2.primeWindow δ Hr, p) ≤ U_max := by
        have h1 : (Fintype.card Alph) ^ Hr ≤ (Fintype.card Alph) ^ H₁ :=
          Nat.pow_le_pow_right Fintype.card_pos hHr_le_H₁
        have h2 := Nat.mul_le_mul h1 hQr_le
        dsimp [U_max]; omega
      have hU_kH : kr * Hr ≤ U_max := by dsimp [U_max]; omega
      have hU_Q : ∏ p ∈ Erdos67H2.primeWindow δ Hr, p ≤ U_max := by
        have h1 : 1 ≤ (Fintype.card Alph) ^ H₁ := Nat.one_le_pow H₁ _ Fintype.card_pos
        have h2 : Q_all ≤ (Fintype.card Alph) ^ H₁ * Q_all := Nat.le_mul_of_pos_left Q_all h1
        dsimp [U_max]; omega
      have herr_r : 4 * (U_max : ℝ) * Real.sqrt (3 * (U_max : ℝ) / (Nat.sqrt X : ℝ)) ≤
          c / (4 * Real.log (Hr : ℝ)) := by
        refine herr_all.trans ?_
        exact div_le_div_of_nonneg_left hc.le (by positivity)
          (mul_le_mul_of_nonneg_left (Real.log_le_log hHr_pos (by exact_mod_cast hHr_le_H₁)) (by norm_num))
      have : ∀ p : Erdos67H2.primeWindow δ Hr, NeZero p.1 :=
        fun p => ⟨(Finset.mem_filter.mp p.2).2.ne_zero⟩
      have hdec := Erdos67H2.entropy_decrement_step hc hδ0 hδ14 hHr_ge rfl hX100
        hU_prod hU_kH hU_Q hU_le_sq herr_r f
      have hbad := hall r hr
      have hbad_div : c / Real.log (Hr : ℝ) <
          (Real.log (Fintype.card (∀ p : Erdos67H2.primeWindow δ Hr, ZMod p.1) : ℝ) -
            (Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
              (fun n => (Erdos67H2.blockOf Hr f n, fun p : Erdos67H2.primeWindow δ Hr => (n : ZMod p.1)))) -
             Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
              (Erdos67H2.blockOf Hr f)))) / (Hr : ℝ) := by
        rw [lt_div_iff₀ hHr_pos]
        have heq : c / Real.log (Hr : ℝ) * (Hr : ℝ) = c * (Hr : ℝ) / Real.log (Hr : ℝ) := by ring
        linarith
      change (c / 4) / Real.log (Hr : ℝ) <
        Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
          (Erdos67H2.blockOf Hr f)) / (Hr : ℝ) -
        Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
          (Erdos67H2.blockOf (kr * Hr) f)) / ((kr * Hr : ℕ) : ℝ)
      have hsub4 : (c / 4) / Real.log (Hr : ℝ) = c / Real.log (Hr : ℝ) - (3 * c / 4) / Real.log (Hr : ℝ) := by
        ring
      linarith
    have hsum_lt : ∑ r ∈ Finset.range R, (c / 4) / Real.log (Erdos67H2.scaleSeq c H_start r : ℝ) <
        Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
          (Erdos67H2.blockOf H_start f)) / (H_start : ℝ) -
        Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
          (Erdos67H2.blockOf H₁ f)) / (H₁ : ℝ) := by
      have hne : (Finset.range R).Nonempty := ⟨0, Finset.mem_range.mpr hR_pos⟩
      have h1 := Finset.sum_lt_sum_of_nonempty hne hstep_r
      let F_ent : ℕ → ℝ := fun n =>
        Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
          (Erdos67H2.blockOf (Erdos67H2.scaleSeq c H_start n) f)) /
          (Erdos67H2.scaleSeq c H_start n : ℝ)
      have htele : ∀ n : ℕ, ∑ r ∈ Finset.range n, (F_ent r - F_ent (r + 1)) = F_ent 0 - F_ent n := by
        intro n; induction n with
        | zero => simp
        | succ n ih => rw [Finset.sum_range_succ, ih]; ring
      have hteleR := htele R
      change ∑ r ∈ Finset.range R, (F_ent r - F_ent (r + 1)) =
        Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
          (Erdos67H2.blockOf H_start f)) / (H_start : ℝ) -
        Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
          (Erdos67H2.blockOf H₁ f)) / (H₁ : ℝ) at hteleR
      exact lt_of_lt_of_eq h1 hteleR
    have hupper : Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
          (Erdos67H2.blockOf H_start f)) / (H_start : ℝ) -
        Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
          (Erdos67H2.blockOf H₁ f)) / (H₁ : ℝ) ≤ Real.log (Fintype.card Alph : ℝ) := by
      have hH_start_pos : (0 : ℝ) < (H_start : ℝ) := by exact_mod_cast (show 0 < H_start by omega)
      have h0_le : Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
          (Erdos67H2.blockOf H_start f)) ≤ (H_start : ℝ) * Real.log (Fintype.card Alph : ℝ) := by
        have h1 := Erdos67H2.shannonH_le_log_card
          (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X) (Erdos67H2.blockOf H_start f))
          (fun x => Erdos67H2.dist_nonneg _ _ (fun n _ => Erdos67H2.logProb_nonneg hX100 n) _ x)
          (Erdos67H2.sum_dist_eq_one _ _ (Erdos67H2.sum_logProb_eq_one hX100) _)
        rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] at h1
        exact h1
      have h0_div : Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
          (Erdos67H2.blockOf H_start f)) / (H_start : ℝ) ≤ Real.log (Fintype.card Alph : ℝ) := by
        rw [div_le_iff₀ hH_start_pos]; linarith
      have hR_nn : 0 ≤ Erdos67H2.shannonH (Erdos67H2.dist (Erdos67H2.logWindow X) (Erdos67H2.logProb X)
          (Erdos67H2.blockOf H₁ f)) / (H₁ : ℝ) :=
        div_nonneg (Erdos67H2.shannonH_nonneg _
          (fun x => Erdos67H2.dist_nonneg _ _ (fun n _ => Erdos67H2.logProb_nonneg hX100 n) _ x)
          (fun x => Erdos67H2.dist_le_one _ _ (fun n _ => Erdos67H2.logProb_nonneg hX100 n)
            (Erdos67H2.sum_logProb_eq_one hX100) _ x)) (Nat.cast_nonneg _)
      linarith
    have hlower : Real.log (Fintype.card Alph : ℝ) ≤
        ∑ r ∈ Finset.range R, (c / 4) / Real.log (Erdos67H2.scaleSeq c H_start r : ℝ) := by
      have hterm_lb : ∀ r ∈ Finset.range R,
          (c / 16) * (1 / (((r + M₀ : ℕ) : ℝ) * Real.log ((r + M₀ : ℕ) : ℝ))) ≤
          (c / 4) / Real.log (Erdos67H2.scaleSeq c H_start r : ℝ) := by
        intro r _
        have hHr_ge : (16 / δ ^ 2 + 100 : ℝ) ≤ (Erdos67H2.scaleSeq c H_start r : ℝ) :=
          hH_start_ge.trans (by exact_mod_cast Erdos67H2.scaleSeq_mono c H_start (Nat.zero_le r))
        have hlogHr_pos : 0 < Real.log (Erdos67H2.scaleSeq c H_start r : ℝ) := by
          linarith [(Erdos67H2.chebyshev_P_H_bounds hδ0 hδ14 hHr_ge).1]
        have hbd := Erdos67H2.scaleSeq_log_bound hc hH_start_100 hM₀_H hM₀_C r
        have h1 := one_div_le_one_div_of_le hlogHr_pos hbd
        calc (c / 16) * (1 / (((r + M₀ : ℕ) : ℝ) * Real.log ((r + M₀ : ℕ) : ℝ)))
            = (c / 4) * (1 / (4 * ((r + M₀ : ℕ) : ℝ) * Real.log ((r + M₀ : ℕ) : ℝ))) := by ring
          _ ≤ (c / 4) * (1 / Real.log (Erdos67H2.scaleSeq c H_start r : ℝ)) := by gcongr
          _ = (c / 4) / Real.log (Erdos67H2.scaleSeq c H_start r : ℝ) := by ring
      have hsum_lb := (Finset.sum_le_sum hterm_lb)
      rw [← Finset.mul_sum] at hsum_lb
      have hdiv_ge := Erdos67H2.sum_inv_n_log_n_ge hM₀_16 R
      have hloglog : Real.log (Real.log (M₀ : ℝ)) + 16 * Real.log (Fintype.card Alph : ℝ) / c + 2 ≤
          Real.log (Real.log ((R + M₀ : ℕ) : ℝ)) := by
        have hR_ge : Real.exp (Real.exp (Real.log (Real.log (M₀ : ℝ)) +
            16 * Real.log (Fintype.card Alph : ℝ) / c + 2)) ≤ ((R + M₀ : ℕ) : ℝ) := by
          have h1 : Real.exp (Real.exp (Real.log (Real.log (M₀ : ℝ)) +
              16 * Real.log (Fintype.card Alph : ℝ) / c + 2)) ≤ (R : ℝ) := by
            dsimp [R]; push_cast; linarith [Nat.le_ceil (Real.exp (Real.exp (Real.log (Real.log (M₀ : ℝ)) +
              16 * Real.log (Fintype.card Alph : ℝ) / c + 2)))]
          have h2 : (R : ℝ) ≤ ((R + M₀ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right R M₀
          linarith
        have hlog1 := Real.log_le_log (Real.exp_pos _) hR_ge
        rw [Real.log_exp] at hlog1
        have hlog2 := Real.log_le_log (Real.exp_pos _) hlog1
        rwa [Real.log_exp] at hlog2
      have hfinal : Real.log (Fintype.card Alph : ℝ) ≤
          (c / 16) * (Real.log (Real.log ((R + M₀ : ℕ) : ℝ)) - Real.log (Real.log (M₀ : ℝ))) := by
        have h1 : 16 * Real.log (Fintype.card Alph : ℝ) / c ≤
            Real.log (Real.log ((R + M₀ : ℕ) : ℝ)) - Real.log (Real.log (M₀ : ℝ)) := by linarith
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ c / 16)
        have heq : (c / 16) * (16 * Real.log (Fintype.card Alph : ℝ) / c) = Real.log (Fintype.card Alph : ℝ) := by
          field_simp [hc.ne']
        linarith
      have hmul_div := mul_le_mul_of_nonneg_left hdiv_ge (by positivity : 0 ≤ c / 16)
      exact hfinal.trans (hmul_div.trans hsum_lb)
    exact lt_irrefl _ (lt_of_le_of_lt hlower (lt_of_lt_of_le hsum_lt hupper))
  obtain ⟨r, hr, hgood⟩ := hexists_r
  set H : ℕ := Erdos67H2.scaleSeq c H_start r
  have hH_mem : H ∈ Finset.Icc H₀ H₁ := by
    rw [Finset.mem_Icc]
    exact ⟨le_trans hH₀_le_start (Erdos67H2.scaleSeq_mono c H_start (Nat.zero_le r)),
      Erdos67H2.scaleSeq_mono c H_start (le_of_lt (Finset.mem_range.mp hr))⟩
  have hH_ge : (16 / δ ^ 2 + 100 : ℝ) ≤ (H : ℝ) :=
    hH_start_ge.trans (by exact_mod_cast Erdos67H2.scaleSeq_mono c H_start (Nat.zero_le r))
  refine ⟨H, hH_mem, ?_⟩
  have : ∀ p : Erdos67H2.primeWindow δ H, NeZero p.1 :=
    fun p => ⟨(Finset.mem_filter.mp p.2).2.ne_zero⟩
  exact Erdos67H2.combine_good_scale h H X M hδ0 hδ14 hη0 hH_ge hX100 hM2 hMη g hg hgood
