import FormalConjectures.ErdosProblems.«1081»

/-!
Odoni's negative answer is derived from the lower bound of Blomer and Granville
(Duke Math. J. 135 (2006), Theorem 2): A(x) is at least x / (log x)^α / (log log x)^C
with α = 1 - 2^(-1/3) < 1/2. If A(x) were asymptotic to c x / sqrt(log x), then
(log x)^(1/2 - α) / (log log x)^C would be bounded, and it is not: every positive
power of log x beats every power of log log x.
-/
open Filter Asymptotics

namespace OMA.R_Erdos1081_erdos_1081_R1

/-- The lower bound of Blomer and Granville. -/
def H1 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
  x / Real.log x ^ Erdos1081.alpha / Real.log (Real.log x) ^ C ≤ (Erdos1081.A x : ℝ)

/-- A positive power of log x eventually exceeds any power of log log x. -/
def H2 : Prop := ∀ a C : ℝ, 0 < a →
  Tendsto (fun x : ℝ => Real.log x ^ a / Real.log (Real.log x) ^ C) atTop atTop

theorem alpha_lt_half : Erdos1081.alpha < 1 / 2 := by
  have h : (2 : ℝ) ^ (-1 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 3) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  rw [Real.rpow_neg_one] at h
  unfold Erdos1081.alpha
  linarith

theorem main : H1 → H2 → type_of% @Erdos1081.erdos_1081 := by
  rintro ⟨C, -, hC⟩ h2 ⟨c, hc, hequiv⟩
  obtain ⟨K, hK⟩ := hequiv.isBigO.bound
  have ha : 0 < 1 / 2 - Erdos1081.alpha := by linarith [alpha_lt_half]
  have hbig := (h2 (1 / 2 - Erdos1081.alpha) C ha).eventually_gt_atTop (K * c)
  have hlog : ∀ᶠ x : ℝ in atTop, 1 < Real.log x :=
    Real.tendsto_log_atTop.eventually_gt_atTop 1
  have hloglog : ∀ᶠ x : ℝ in atTop, 0 < Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0
  obtain ⟨x, hlow, hup, hgt, hL, hLL, hx⟩ :=
    (hC.and (hK.and (hbig.and (hlog.and (hloglog.and (eventually_gt_atTop 0)))))).exists
  have hL0 : 0 < Real.log x := by linarith
  have hsq : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hL0
  have hLa : 0 < Real.log x ^ Erdos1081.alpha := Real.rpow_pos_of_pos hL0 _
  have hLC : 0 < Real.log (Real.log x) ^ C := Real.rpow_pos_of_pos hLL _
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (by positivity)] at hup
  have hchain : x / Real.log x ^ Erdos1081.alpha / Real.log (Real.log x) ^ C ≤
      K * (c * x / Real.sqrt (Real.log x)) := hlow.trans hup
  have hrw : Real.log x ^ (1 / 2 - Erdos1081.alpha) / Real.log (Real.log x) ^ C =
      x / Real.log x ^ Erdos1081.alpha / Real.log (Real.log x) ^ C *
        (Real.sqrt (Real.log x) / x) := by
    rw [Real.rpow_sub hL0, ← Real.sqrt_eq_rpow]
    field_simp
  have hrw2 : K * (c * x / Real.sqrt (Real.log x)) * (Real.sqrt (Real.log x) / x) = K * c := by
    field_simp
  have : Real.log x ^ (1 / 2 - Erdos1081.alpha) / Real.log (Real.log x) ^ C ≤ K * c := by
    rw [hrw, ← hrw2]
    exact mul_le_mul_of_nonneg_right hchain (by positivity)
  linarith

end OMA.R_Erdos1081_erdos_1081_R1
