import OMAReductions.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1
import Mathlib

/-! Truncate the logarithm of each Euler factor at the powers p^k ≤ x.
The tangent bound for log log and θ ≤ ψ absorb the endpoint term
of Abel summation. The two analytic inputs separate the Mertens
constant from the normalized increments of the prime-power sum. -/
open Filter Finset Real Set MeasureTheory
namespace OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1_H2_R1

/-- Mertens normalization of the truncated prime-power harmonic sum. -/
def H1 : Prop :=
  let F (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, ∑ k ∈ Finset.range (Nat.log p ⌊x⌋₊),
    ((1:ℝ)/p)^(k+1)/((k:ℝ)+1)
  Tendsto (fun y : ℝ ↦ F y - log (log y)) atTop (nhds eulerMascheroniConstant)

/-- Abel summation of the increments, with the lower endpoint retained.
This statement does not involve Mertens' constant. -/
def H2 : Prop :=
  let F (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, ∑ k ∈ Finset.range (Nat.log p ⌊x⌋₊),
    ((1:ℝ)/p)^(k+1)/((k:ℝ)+1)
  ∀ᶠ x : ℝ in atTop,
    Tendsto (fun y : ℝ ↦ F y - F x - (log (log y) - log (log x))) atTop
      (nhds ((∫ t in Ioi x, (Chebyshev.psi t-t)*((1/log t+1/(log t)^2)/t^2)) -
        (Chebyshev.psi x-x)/(x*log x)))

theorem tangent {s x : ℝ} (hs : 0<s) (hx : 0<x) :
    log s - log x ≤ (s-x)/x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hs hx)
  rw [Real.log_div hs.ne' hx.ne'] at h
  simpa only [sub_div,div_self hx.ne'] using h

theorem loglog_tangent {s x : ℝ} (hs : 1<s) (hx : 1<x) :
    log (log s)-log (log x) ≤ (s-x)/(x*log x) := by
  have hl := Real.log_pos hx
  calc
    _ ≤ (log s-log x)/log x := tangent (Real.log_pos hs) hl
    _ ≤ ((s-x)/x)/log x := div_le_div_of_nonneg_right (tangent (by linarith) (by linarith)) hl.le
    _ = _ := by ring

theorem prime_log_truncation {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (∑ k ∈ range m, ((1:ℝ)/p)^(k+1)/((k:ℝ)+1)) ≤ -log (1-1/(p:ℝ)) := by
  have h1 : 1<(p:ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : 0<(p:ℝ) := by linarith
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x:=1/(p:ℝ))
    (by rw [abs_of_pos (by positivity)]; exact (div_lt_one hp0).mpr h1)
  rw [← hs.tsum_eq]
  exact hs.summable.sum_le_tsum _ (fun k _ ↦ by positivity)

theorem theta_large {x : ℝ} (hx : 3≤x) : 1<Chebyshev.theta x := by
  have t : log (3:ℝ) ≤ Chebyshev.theta (3:ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    have h3 : (3:ℕ) ∈ Nat.primesLE ⌊(3:ℝ)⌋₊ := by norm_num <;> decide
    have h := Finset.single_le_sum (f:=fun q : ℕ ↦ log (q:ℝ))
      (fun q hq ↦ Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hq).one_le)) h3
    simpa using h
  exact ((Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ)<3)).mpr Real.exp_one_lt_three).trans_le
    (t.trans (Chebyshev.theta_mono hx))

theorem main : H1 → H2 → OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro hm ha
  let F (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, ∑ k ∈ Finset.range (Nat.log p ⌊x⌋₊),
    ((1:ℝ)/p)^(k+1)/((k:ℝ)+1)
  have mertens : Tendsto (fun y : ℝ ↦ F y - log (log y)) atTop (nhds eulerMascheroniConstant) := hm
  filter_upwards [ha,eventually_ge_atTop (3:ℝ)] with x hab hx
  have tx := theta_large hx
  have xp : 0<x := by linarith
  have lx : 0<log x := Real.log_pos (by linarith)
  have analytic : Tendsto (fun y : ℝ ↦ F y - F x - (log (log y) - log (log x))) atTop
      (nhds (eulerMascheroniConstant - F x + log (log x))) := by
    convert (mertens.sub_const (F x)).add_const (log (log x)) using 1
    funext y
    ring
  change Tendsto (fun y : ℝ ↦ F y - F x - (log (log y) - log (log x))) atTop _ at hab
  have endpoint := tendsto_nhds_unique analytic hab
  have positive (p : ℕ) (hp : p ∈ Nat.primesLE ⌊x⌋₊) : 0<1-1/(p:ℝ) := by
    have one : 1<(p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr one)
  have product : log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ))) ≤ -F x := by
    rw [Real.log_prod (fun p hp ↦ (positive p hp).ne')]
    dsimp only [F]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro p hp
    linarith [prime_log_truncation (Nat.prime_of_mem_primesLE hp) (Nat.log p ⌊x⌋₊)]
  have geom : log (log (Chebyshev.theta x))-log (log x) ≤ (Chebyshev.psi x-x)/(x*log x) :=
    (loglog_tangent tx (by linarith)).trans (div_le_div_of_nonneg_right
      (sub_le_sub_right (Chebyshev.theta_le_psi x) x) (mul_nonneg xp.le lx.le))
  have prodPos : 0 < ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ)) := Finset.prod_pos positive
  rw [Real.log_mul (mul_ne_zero (Real.exp_pos _).ne' (Real.log_pos tx).ne') prodPos.ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.log_pos tx).ne',Real.log_exp]
  linarith [show (0:ℝ)≤4/x by positivity]

end OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1_H2_R1
