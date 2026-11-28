import OMAStatements.S_mo_297054
import Mathlib

/-!
# Krzyz conjecture: the sharp case n = 1

Proved here (`krzyz_one_strict`, `krzyz_n1`): for f holomorphic, nonvanishing, |f| <= 1 on the
unit disk, |f'(0)| <= 2 |f(0)| log(1/|f(0)|) (when |f(0)| < 1) and |f'(0)| <= 2/e.
Proof: holomorphic logarithm f = exp L (Morera primitive of f'/f), Re L <= 0, Schwarz lemma for
the Mobius map (w - a)/(w + conj a) composed with L, then s e^(-s) <= 1/e.
H1: the known cases 2 <= n <= 5. H2: the open cases n >= 6.
-/

namespace OMA.R_mo_297054_R1

open Metric Complex

/-- Holomorphic logarithm of a nonvanishing holomorphic function on the unit disk. -/
lemma holo_log (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (ball 0 1))
    (hne : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0) :
    ∃ L : ℂ → ℂ, L 0 = Complex.log (g 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasDerivAt L (deriv g z / g z) z) ∧
      (∀ z ∈ ball (0 : ℂ) 1, g z = Complex.exp (L z)) := by
  have hq : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball 0 1) :=
    (hg.deriv isOpen_ball).div hg hne
  obtain ⟨L, hL0, hL⟩ := (hq.isExactOn_ball).with_val_at 0 (Complex.log (g 0))
  refine ⟨L, hL0, hL, ?_⟩
  have hφ : ∀ z ∈ ball (0 : ℂ) 1,
      HasDerivAt (fun w => g w * Complex.exp (-(L w))) 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z :=
      ((hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have h3 : HasDerivAt (fun w => g w * Complex.exp (-(L w)))
        (deriv g z * Complex.exp (-(L z)) +
          g z * (Complex.exp (-(L z)) * -(deriv g z / g z))) z :=
      hgz.mul (hL z hz).neg.cexp
    refine h3.congr_deriv ?_
    rw [div_eq_mul_inv]
    linear_combination (-(deriv g z * Complex.exp (-(L z)))) * mul_inv_cancel₀ (hne z hz)
  have hconst : ∀ z ∈ ball (0 : ℂ) 1,
      g z * Complex.exp (-(L z)) = g 0 * Complex.exp (-(L 0)) := by
    intro z hz
    refine isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      (fun w hw => (hφ w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hφ w hw).deriv) hz (mem_ball_self one_pos)
  intro z hz
  have h1 := hconst z hz
  rw [hL0] at h1
  simp only [Complex.exp_neg] at h1
  rw [Complex.exp_log (hne 0 (mem_ball_self one_pos)),
    mul_inv_cancel₀ (hne 0 (mem_ball_self one_pos))] at h1
  have hE : Complex.exp (L z) ≠ 0 := Complex.exp_ne_zero _
  field_simp at h1
  exact h1

/-- Möbius map of the closed left half-plane into the closed unit disk. -/
lemma mobius_le (a w : ℂ) (ha : a.re < 0) (hw : w.re ≤ 0) :
    ‖(w - a) / (w + (starRingEnd ℂ) a)‖ ≤ 1 := by
  have hd : w + (starRingEnd ℂ) a ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [norm_div, div_le_one (norm_pos_iff.mpr hd)]
  have key : ‖w - a‖ ^ 2 ≤ ‖w + (starRingEnd ℂ) a‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp key

/-- Core estimate: `|g'(0)| ≤ 2 |g(0)| log (1/|g(0)|)` when `|g(0)| < 1`. -/
theorem krzyz_one_strict (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0 ∧ ‖g z‖ ≤ 1) (h0 : ‖g 0‖ < 1) :
    ‖deriv g 0‖ ≤ 2 * ‖g 0‖ * Real.log (1 / ‖g 0‖) := by
  have m0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  obtain ⟨L, hL0, hL, hexp⟩ := holo_log g hg (fun z hz => (hb z hz).1)
  have hg0 : g 0 ≠ 0 := (hb 0 m0).1
  have hre : ∀ z ∈ ball (0 : ℂ) 1, (L z).re ≤ 0 := by
    intro z hz
    have h := (hb z hz).2
    rw [hexp z hz, Complex.norm_exp] at h
    exact Real.exp_le_one_iff.mp h
  set a := L 0 with ha_def
  have hare : a.re = Real.log ‖g 0‖ := by rw [hL0, Complex.log_re]
  have hpos : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have ha : a.re < 0 := by rw [hare]; exact Real.log_neg hpos h0
  set ψ : ℂ → ℂ := fun w => (w - a) / (w + (starRingEnd ℂ) a) with hψ
  have hden : ∀ w : ℂ, w.re ≤ 0 → w + (starRingEnd ℂ) a ≠ 0 := by
    intro w hw h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hψd : ∀ w : ℂ, w.re ≤ 0 → HasDerivAt ψ
      ((1 * (w + (starRingEnd ℂ) a) - (w - a) * 1) / (w + (starRingEnd ℂ) a) ^ 2) w := by
    intro w hw
    exact ((hasDerivAt_id w).sub_const a).div ((hasDerivAt_id w).add_const _) (hden w hw)
  have hF : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt (fun z => ψ (L z))
      (((1 * (L z + (starRingEnd ℂ) a) - (L z - a) * 1) / (L z + (starRingEnd ℂ) a) ^ 2)
        * (deriv g z / g z)) z := by
    intro z hz
    exact (hψd (L z) (hre z hz)).comp z (hL z hz)
  have hFd : DifferentiableOn ℂ (fun z => ψ (L z)) (ball 0 1) :=
    fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  have hF0 : ψ (L 0) = 0 := by simp [hψ, ← ha_def]
  have hmaps : Set.MapsTo (fun z => ψ (L z)) (ball 0 1) (closedBall (ψ (L 0)) 1) := by
    intro z hz
    rw [hF0, mem_closedBall, dist_zero_right]
    exact mobius_le a (L z) ha (hre z hz)
  have hS := Complex.norm_deriv_le_div_of_mapsTo_ball hFd hmaps one_pos
  rw [(hF 0 m0).deriv, ← ha_def, Complex.add_conj] at hS
  have hre0 : ((2 * a.re : ℝ) : ℂ) ≠ 0 := by
    have : 2 * a.re ≠ 0 := by linarith
    exact_mod_cast this
  have hsimp : (1 * ((2 * a.re : ℝ) : ℂ) - (a - a) * 1) / ((2 * a.re : ℝ) : ℂ) ^ 2
      = 1 / ((2 * a.re : ℝ) : ℂ) := by
    field_simp
    ring
  rw [hsimp, norm_mul, norm_div, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg (by linarith : 2 * a.re < 0)] at hS
  have h1 : ‖deriv g 0‖ ≤ (-(2 * a.re)) * ‖g 0‖ := by
    have hpos2 : 0 < -(2 * a.re) := by linarith
    rw [div_one, one_div, inv_mul_le_iff₀ hpos2, mul_one, div_le_iff₀ hpos] at hS
    exact hS
  have hlog : Real.log (1 / ‖g 0‖) = - a.re := by
    rw [one_div, Real.log_inv, hare]
  rw [hlog]
  linarith [h1]

/-- `x log(1/x) ≤ 1/e` for `x > 0`. -/
lemma xlog_le (x : ℝ) (hx : 0 < x) : x * Real.log (1 / x) ≤ Real.exp (-1) := by
  set t := Real.log (1 / x) with ht
  have hx' : x = Real.exp (-t) := by
    rw [ht, one_div, Real.log_inv, neg_neg, Real.exp_log hx]
  have h1 : t ≤ Real.exp (t - 1) := by linarith [Real.add_one_le_exp (t - 1)]
  have h2 : Real.exp (t - 1) * Real.exp (-t) = Real.exp (-1) := by
    rw [← Real.exp_add]; ring_nf
  rw [hx']
  nlinarith [Real.exp_pos (-t)]

/-- The sharp case `n = 1` of the Krzyż conjecture: `|f'(0)| ≤ 2/e`. -/
theorem krzyz_n1 (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0 ∧ ‖f z‖ ≤ 1) :
    ‖deriv f 0‖ ≤ 2 / Real.exp 1 := by
  have m0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hfd : DifferentiableAt ℂ f 0 := (hf 0 m0).differentiableAt (isOpen_ball.mem_nhds m0)
  have hE : 2 / Real.exp 1 = 2 * Real.exp (-1) := by
    rw [Real.exp_neg]; ring
  have key : ∀ r : ℝ, 0 < r → r < 1 → r * ‖deriv f 0‖ ≤ 2 / Real.exp 1 := by
    intro r hr0 hr1
    set g : ℂ → ℂ := fun z => (r : ℂ) * f z with hg_def
    have hgd : DifferentiableOn ℂ g (ball 0 1) := hf.const_mul _
    have hgb : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0 ∧ ‖g z‖ ≤ 1 := by
      intro z hz
      refine ⟨mul_ne_zero (by exact_mod_cast hr0.ne') (hb z hz).1, ?_⟩
      rw [hg_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith [(hb z hz).2, norm_nonneg (f z)]
    have hgn : ‖g 0‖ = r * ‖f 0‖ := by
      rw [hg_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    have hg0 : ‖g 0‖ < 1 := by
      rw [hgn]; nlinarith [(hb 0 m0).2, norm_nonneg (f 0)]
    have hder : deriv g 0 = (r : ℂ) * deriv f 0 := deriv_const_mul _ hfd
    have h := krzyz_one_strict g hgd hgb hg0
    rw [hder, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] at h
    have hp : 0 < ‖g 0‖ := norm_pos_iff.mpr (hgb 0 m0).1
    have hx := xlog_le _ hp
    rw [hE]
    nlinarith
  by_contra hcon
  push Not at hcon
  set c := 2 / Real.exp 1 with hc
  have hc0 : 0 < c := by positivity
  set d := ‖deriv f 0‖
  have hd : 0 < d := lt_trans hc0 hcon
  have h := key ((c + d) / (2 * d)) (by positivity)
    (by rw [div_lt_one (by positivity)]; linarith)
  have : (c + d) / (2 * d) * d = (c + d) / 2 := by field_simp
  rw [this] at h
  linarith

/-- Known cases `2 ≤ n ≤ 5` (Hummel-Scheinberg-Zalcman 1977, Tan 1983, Samaris 2003). -/
def H1 : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) →
    (∀ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0 ∧ ‖f z‖ ≤ 1) →
    ∀ n : ℕ, 2 ≤ n → n ≤ 5 → ‖iteratedDeriv n f 0 / n.factorial‖ ≤ 2 / Real.exp 1

/-- The open cases `n ≥ 6`. -/
def H2 : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) →
    (∀ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0 ∧ ‖f z‖ ≤ 1) →
    ∀ n : ℕ, 6 ≤ n → ‖iteratedDeriv n f 0 / n.factorial‖ ≤ 2 / Real.exp 1

theorem main : H1 → H2 → type_of% @OMA.S_mo_297054.main := by
  intro h1 h2 f hf hb n hn
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    simpa [iteratedDeriv_one] using krzyz_n1 f hf hb
  · rcases Nat.lt_or_ge n 6 with h' | h'
    · exact h1 f hf hb n h (by omega)
    · exact h2 f hf hb n h'

end OMA.R_mo_297054_R1
