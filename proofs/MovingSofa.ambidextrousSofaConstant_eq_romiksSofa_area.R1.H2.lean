import OMAReductions.R_MovingSofa_ambidextrousSofaConstant_eq_romiksSofa_area_R1
import Mathlib

/-
Adapted from the merged proof of MovingSofa.romiksSofa_area_le_ambidextrousSofaConstant in
GuillaumeBAUD-coder/open-math-agents by senamakel, which is itself adapted from
github.com/vltanh/lean4-ambidextrous-sofa (commit 5e90d029cab30151441a5794db31423bc277aad8),
(c) The-Anh Vu-Le (vltanh), used under Apache-2.0.
The construction of Romik's ambidextrous sofa and its area 1 + 4Y^2 + arctan Y are theirs.
Change: only the final statement, the existence step H2 of moon-4's reduction R1.
The proof that Romik ambidextrous sofa is an ambidextrous sofa of area 1 + 4Y^2 + arctan Y is theirs (AmbidextrousSofa/Reference/*, Geometry/*, Measure/*, Analysis/* and the FormalConjectures/Bridge.lean bridge), itself following Romik, Differential equations and exact solutions in the moving sofa problem (2018).
Submitted to lefttosolve.com by senamakel; ported to Lean v4.33.1 / Mathlib 0df444a / formal-conjectures 9097e2f.
Changes: flattened the 46 modules on the path of the lower bound into one file (module and public import lines removed, each file wrapped in a section), stripped comments, removed expose, simp and local fun_prop attributes (the needed simp lemmas and continuity hypotheses are passed explicitly), replaced two Mathlib lemmas that are newer than the pin (composition of a Lipschitz map with an absolutely continuous function, congruence for absolutely continuous functions, ite_eq_left and ite_eq_right as if_pos and if_neg), used stdSimplex instead of Convexity.StdSimplex in the Caratheodory compactness step, used ContinuousAffineMap.decompLinearIsometryEquiv in place of decompHomeomorph, and kept only the lower-bound half of the FormalConjectures bridge (the upper bound and uniqueness are not needed).
-/

theorem ac_comp_lip {g f : ℝ → ℝ} {K : NNReal} {s : Set ℝ} {a b : ℝ}
    (hg : LipschitzOnWith K g s) (hmaps : Set.MapsTo f (Set.uIcc a b) s)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hsum => ?_⟩
  have h1 := h E hE hsum
  calc ∑ i ∈ Finset.range E.1, dist (g (f (E.2 i).1)) (g (f (E.2 i).2))
      ≤ ∑ i ∈ Finset.range E.1, K * dist (f (E.2 i).1) (f (E.2 i).2) := by
        apply Finset.sum_le_sum
        intro i hi
        have := hg.dist_le_mul _ (hmaps (hE.left i hi).left) _ (hmaps (hE.left i hi).right)
        exact this
    _ = K * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by rw [Finset.mul_sum]
    _ ≤ K * (ε / (K + 1)) := by gcongr
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field_simp

theorem ac_congr {f g : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (h : ∀ x ∈ Set.uIcc a b, f x = g x) : AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hs => ?_⟩
  have := H E hE hs
  convert this using 2 with i hi
  rw [h _ (hE.left i hi).left, h _ (hE.left i hi).right]

theorem ite_eq_left {P : Prop} [Decidable P] {α : Sort _} {a b : α} (h : P) : (if P then a else b) = a := if_pos h
theorem ite_eq_right {P : Prop} [Decidable P] {α : Sort _} {a b : α} (h : ¬P) : (if P then a else b) = b := if_neg h

section BP0

noncomputable section BPn0

namespace AmbidextrousSofa

def cubic (y : ℝ) : ℝ := 4 * y ^ 3 + 3 * y - 1

theorem cubic_strictMono : StrictMono cubic := fun x y hxy => by
  unfold cubic; nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]

theorem exists_positive_root : ∃ y : ℝ, 0 < y ∧ cubic y = 0 := by
  obtain ⟨y, hy, heq⟩ := intermediate_value_Icc (by norm_num : (2 / 7 : ℝ) ≤ 3 / 10)
    (by unfold cubic; fun_prop : Continuous cubic).continuousOn
    (by norm_num [cubic] : (0 : ℝ) ∈ Set.Icc (cubic (2 / 7)) (cubic (3 / 10)))
  exact ⟨y, by linarith [hy.1], heq⟩

def Y : ℝ := Classical.choose exists_positive_root

theorem Y_pos : 0 < Y := (Classical.choose_spec exists_positive_root).1

theorem Y_cubic : cubic Y = 0 := (Classical.choose_spec exists_positive_root).2

theorem Y_equation : 4 * Y ^ 3 + 3 * Y = 1 := sub_eq_zero.mp Y_cubic

theorem two_sevenths_lt_Y : (2 / 7 : ℝ) < Y :=
  cubic_strictMono.lt_iff_lt.mp (by rw [Y_cubic]; norm_num [cubic])

theorem Y_lt_three_tenths : Y < (3 / 10 : ℝ) :=
  cubic_strictMono.lt_iff_lt.mp (by rw [Y_cubic]; norm_num [cubic])

theorem Y_ne_zero : Y ≠ 0 := Y_pos.ne'

def beta : ℝ := Real.arctan Y

theorem beta_pos : 0 < beta := Real.arctan_pos.mpr Y_pos

theorem beta_lt_pi_div_two : beta < Real.pi / 2 := Real.arctan_lt_pi_div_two Y

theorem beta_lt_pi_div_four : beta < Real.pi / 4 := by
  rw [beta, ← Real.arctan_one]
  exact Real.arctan_strictMono (by linarith [Y_lt_three_tenths])

theorem tan_beta : Real.tan beta = Y := Real.tan_arctan Y

def M : ℝ := 1 + 4 * Y ^ 2 + beta

theorem M_sub_beta_add_two_mul_Y : (M - beta + 2) * Y = 1 := by
  unfold M; linear_combination Y_equation

end AmbidextrousSofa

end BPn0

end BP0

section BP1

noncomputable section BPn1

namespace AmbidextrousSofa.Reference

def sinBeta : ℝ := Real.sin beta

def cosBeta : ℝ := Real.cos beta

def A : ℝ := 1 / (4 * sinBeta)

def k : ℝ := 1 - 4 / 3 * A

def T : ℝ := 3 / 2 * (Real.pi / 4 - beta)

def R : ℝ := cosBeta / Real.cos T

def lateSwitch : ℝ := Real.pi / 2 - beta

theorem sinBeta_pos : 0 < sinBeta :=
  Real.sin_pos_of_pos_of_lt_pi beta_pos (by linarith [beta_lt_pi_div_two, Real.pi_pos])

theorem cosBeta_pos : 0 < cosBeta := Real.cos_arctan_pos Y

theorem sinBeta_ne_zero : sinBeta ≠ 0 := sinBeta_pos.ne'

theorem sinBeta_eq_Y_mul_cosBeta : sinBeta = Y * cosBeta := by
  rw [← tan_beta, Real.tan_eq_sin_div_cos]
  exact (div_mul_cancel₀ _ cosBeta_pos.ne').symm

theorem A_pos : 0 < A := div_pos one_pos (mul_pos four_pos sinBeta_pos)

theorem four_mul_A_mul_sinBeta : 4 * A * sinBeta = 1 := by
  unfold A; field_simp [sinBeta_ne_zero]

theorem A_mul_cosBeta : A * cosBeta = 1 / (4 * Y) := by
  rw [A, sinBeta_eq_Y_mul_cosBeta]; field_simp [cosBeta_pos.ne', Y_ne_zero]

theorem A_mul_cosBeta_lt_seven_eighths : A * cosBeta < 7 / 8 := by
  rw [A_mul_cosBeta, div_lt_iff₀ (mul_pos four_pos Y_pos)]; linarith [two_sevenths_lt_Y]

theorem cos_T_pos : 0 < Real.cos T := by
  apply Real.cos_pos_of_mem_Ioo; unfold T
  constructor <;> linarith [beta_pos, beta_lt_pi_div_four, Real.pi_pos]

theorem R_pos : 0 < R := div_pos cosBeta_pos cos_T_pos

theorem beta_lt_lateSwitch : beta < lateSwitch := by
  unfold lateSwitch; linarith [beta_lt_pi_div_four]

theorem lateSwitch_lt_pi_div_two : lateSwitch < Real.pi / 2 := by
  unfold lateSwitch; linarith [beta_pos]

theorem lateSwitch_pos : 0 < lateSwitch := beta_pos.trans beta_lt_lateSwitch

theorem firstPhaseAngle_eq_arctan_two_Y :
    beta / 2 + Real.pi / 8 = Real.arctan (2 * Y) := by
  have hY1 : Y < 1 := by linarith [Y_lt_three_tenths]
  have htwo : 2 * Y < 1 := by linarith [Y_lt_three_tenths]
  have hden : 1 - (2 * Y) ^ 2 ≠ 0 := by nlinarith [Y_pos, Y_lt_three_tenths]
  have hden1 : 1 - Y * 1 ≠ 0 := by linarith
  have hquot : 2 * (2 * Y) / (1 - (2 * Y) ^ 2) = (Y + 1) / (1 - Y * 1) := by
    apply (div_eq_div_iff hden hden1).mpr
    nlinarith [Y_equation]
  have hdouble := Real.two_mul_arctan (x := 2 * Y) (by linarith [Y_pos]) htwo
  rw [hquot, ← Real.arctan_add (show Y * 1 < 1 by linarith), Real.arctan_one] at hdouble
  unfold beta
  linarith

theorem firstPhase_sin_eq_two_Y_mul_cos :
    Real.sin (beta / 2 + Real.pi / 8) = 2 * Y * Real.cos (beta / 2 + Real.pi / 8) := by
  rw [firstPhaseAngle_eq_arctan_two_Y]
  have ht := Real.tan_arctan (2 * Y)
  rw [Real.tan_eq_sin_div_cos] at ht
  exact (div_eq_iff (Real.cos_arctan_pos _).ne').mp ht

theorem firstSwitch_eqs :
    R * Real.cos (beta / 2 + Real.pi / 8) = 4 / 3 * A * Real.cos beta ∧
      R * Real.sin (beta / 2 + Real.pi / 8) = 2 / 3 ∧ 4 * A * Real.sin beta = 1 := by
  have hR : R * Real.cos T = Real.cos beta := div_mul_cancel₀ _ cos_T_pos.ne'
  have hY : Real.sin beta = Y * Real.cos beta := sinBeta_eq_Y_mul_cosBeta
  have hphase := firstPhase_sin_eq_two_Y_mul_cos
  have hangle : T = Real.pi / 2 - (beta + (beta / 2 + Real.pi / 8)) := by unfold T; ring
  have hcos : Real.cos T = 3 / 2 * Real.cos beta * Real.sin (beta / 2 + Real.pi / 8) := by
    rw [hangle, Real.cos_pi_div_two_sub, Real.sin_add, hY, hphase]
    ring
  rw [hcos] at hR
  have hs : R * Real.sin (beta / 2 + Real.pi / 8) = 2 / 3 := by
    apply mul_left_cancel₀ (show Real.cos beta ≠ 0 from cosBeta_pos.ne')
    linear_combination (2 / 3) * hR
  have hA : 4 * A * Real.sin beta = 1 := four_mul_A_mul_sinBeta
  refine ⟨?_, hs, hA⟩
  rw [hY] at hA
  apply mul_left_cancel₀ Y_ne_zero
  linear_combination -(R / 2) * hphase + hs / 2 - hA / 3

theorem R_mul_sin_firstPhase :
    R * Real.sin (beta / 2 + Real.pi / 8) = 2 / 3 := firstSwitch_eqs.2.1

theorem lateSwitch_trig :
    Real.sin (lateSwitch / 2 + Real.pi / 8) = Real.cos (beta / 2 + Real.pi / 8) ∧
      Real.cos (lateSwitch / 2 + Real.pi / 8) = Real.sin (beta / 2 + Real.pi / 8) ∧
      Real.sin lateSwitch = Real.cos beta ∧ Real.cos lateSwitch = Real.sin beta := by
  rw [show lateSwitch / 2 + Real.pi / 8 = Real.pi / 2 - (beta / 2 + Real.pi / 8) by
    unfold lateSwitch; ring, lateSwitch]
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, and_self]

end AmbidextrousSofa.Reference

end BPn1

end BP1

section BP2

noncomputable section BPn2

open Set
open scoped Topology

namespace AmbidextrousSofa

theorem hasDerivAt_if_le (c : ℝ) {f g fD gD : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (fD x) x) (hg : ∀ x, HasDerivAt g (gD x) x)
    (hvalue : f c = g c) (hderiv : fD c = gD c) (x : ℝ) :
    HasDerivAt (fun y => if y ≤ c then f y else g y)
      (if x ≤ c then fD x else gD x) x := by
  rcases lt_trichotomy x c with hlt | rfl | hgt
  · rw [ite_eq_left hlt.le]
    exact (hf x).congr_of_eventuallyEq ((eventually_lt_nhds hlt).mono fun y hy => ite_eq_left hy.le)
  · have hright : ∀ y ∈ Ici x, (if y ≤ x then f y else g y) = g y := fun y hy => by
      split_ifs with h <;> [rw [le_antisymm h hy, hvalue]; rfl]
    rw [ite_eq_left le_rfl, ← hasDerivWithinAt_univ, ← Iic_union_Ici]
    exact ((hf x).hasDerivWithinAt.congr (fun y (hy : y ≤ x) => ite_eq_left hy)
      (ite_eq_left le_rfl)).union
      (((hg x).congr_deriv hderiv.symm).hasDerivWithinAt.congr hright (hright x (Set.mem_Ici.2 le_rfl)))
  · rw [ite_eq_right (not_le.mpr hgt)]
    exact (hg x).congr_of_eventuallyEq
      ((eventually_gt_nhds hgt).mono fun y hy => ite_eq_right (not_le.mpr hy))

def joinThree (c d : ℝ) (E N W : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ c then E t else if t ≤ d then N t else W t

theorem continuous_joinThree {c d : ℝ} {E N W : ℝ → ℝ}
    (hcd : c ≤ d) (hE : Continuous E) (hN : Continuous N) (hW : Continuous W)
    (hfirst : E c = N c) (hlast : N d = W d) :
    Continuous (joinThree c d E N W) :=
  hE.if_le (hN.if_le hW continuous_id continuous_const fun _ (h : _ = _) => h ▸ hlast)
    continuous_id continuous_const fun _ (h : _ = _) => by rw [h, ite_eq_left hcd, hfirst]

theorem hasDerivAt_joinThree {c d : ℝ} {E N W ED ND WD : ℝ → ℝ} (hcd : c ≤ d)
    (hE : ∀ t, HasDerivAt E (ED t) t) (hN : ∀ t, HasDerivAt N (ND t) t)
    (hW : ∀ t, HasDerivAt W (WD t) t) (hfirst : E c = N c) (hlast : N d = W d)
    (hfirstD : ED c = ND c) (hlastD : ND d = WD d) (t : ℝ) :
    HasDerivAt (joinThree c d E N W) (joinThree c d ED ND WD t) t :=
  hasDerivAt_if_le c hE (hasDerivAt_if_le d hN hW hlast hlastD)
    (by rw [ite_eq_left hcd, hfirst]) (by rw [ite_eq_left hcd, hfirstD]) t

end AmbidextrousSofa

namespace AmbidextrousSofa.Reference

def fEarly (t : ℝ) : ℝ := Real.cos t + 1 / 2 * Real.sin t

def gEarly (t : ℝ) : ℝ := (2 * A - 1) * Real.sin t + 1 / 2 * Real.cos t + 1 / 2

def fMiddle (t : ℝ) : ℝ :=
  R * Real.cos (t / 2 + Real.pi / 8) + k * Real.cos t + 1 / 2 * Real.sin t

def gMiddle (t : ℝ) : ℝ :=
  R * Real.sin (t / 2 + Real.pi / 8) - k * Real.sin t + 1 / 2 * Real.cos t

def fLate (t : ℝ) : ℝ :=
  (1 - 2 / 3 * A) * Real.cos t + 1 / 2 * Real.sin t + 1 / 2

def gLate (t : ℝ) : ℝ := (8 / 3 * A - 1) * Real.sin t + 1 / 2 * Real.cos t

def fEarlyD (t : ℝ) : ℝ := -Real.sin t + 1 / 2 * Real.cos t

def gEarlyD (t : ℝ) : ℝ := (2 * A - 1) * Real.cos t - 1 / 2 * Real.sin t

def fMiddleD (t : ℝ) : ℝ :=
  -(R / 2) * Real.sin (t / 2 + Real.pi / 8) - k * Real.sin t + 1 / 2 * Real.cos t

def gMiddleD (t : ℝ) : ℝ :=
  R / 2 * Real.cos (t / 2 + Real.pi / 8) - k * Real.cos t - 1 / 2 * Real.sin t

def fLateD (t : ℝ) : ℝ := -(1 - 2 / 3 * A) * Real.sin t + 1 / 2 * Real.cos t

def gLateD (t : ℝ) : ℝ := (8 / 3 * A - 1) * Real.cos t - 1 / 2 * Real.sin t

def referenceF (t : ℝ) : ℝ :=
  if t ≤ beta then fEarly t else if t ≤ lateSwitch then fMiddle t else fLate t

def referenceG (t : ℝ) : ℝ :=
  if t ≤ beta then gEarly t else if t ≤ lateSwitch then gMiddle t else gLate t

def referenceFD (t : ℝ) : ℝ :=
  if t ≤ beta then fEarlyD t else if t ≤ lateSwitch then fMiddleD t else fLateD t

def referenceGD (t : ℝ) : ℝ :=
  if t ≤ beta then gEarlyD t else if t ≤ lateSwitch then gMiddleD t else gLateD t

theorem phases_eq_right {p q r : ℝ → ℝ} (h₁ : p beta = q beta)
    (h₂ : q lateSwitch = r lateSwitch) (t : ℝ) :
    (if t ≤ beta then p t else if t ≤ lateSwitch then q t else r t) =
      if t < beta then p t else if t < lateSwitch then q t else r t := by
  have := beta_lt_lateSwitch
  split_ifs <;> first
    | rfl | (exfalso; linarith)
    | (rw [show t = beta by linarith]; exact h₁) | (rw [show t = lateSwitch by linarith]; exact h₂)

theorem hasDerivAt_middlePhaseAngle (t : ℝ) :
    HasDerivAt (fun x : ℝ => x / 2 + Real.pi / 8) (1 / 2) t := by
  simpa only [one_div] using ((hasDerivAt_id' t).div_const 2).add_const (Real.pi / 8)

theorem f_matching_first : fEarly beta = fMiddle beta := by
  unfold fMiddle fEarly k; linear_combination -firstSwitch_eqs.1

theorem g_matching_first : gEarly beta = gMiddle beta := by
  unfold gMiddle gEarly k; linear_combination firstSwitch_eqs.2.2 / 6 - firstSwitch_eqs.2.1

theorem fD_matching_first : fEarlyD beta = fMiddleD beta := by
  unfold fMiddleD fEarlyD k; linear_combination firstSwitch_eqs.2.1 / 2 - firstSwitch_eqs.2.2 / 3

theorem gD_matching_first : gEarlyD beta = gMiddleD beta := by
  unfold gMiddleD gEarlyD k; linear_combination -firstSwitch_eqs.1 / 2

theorem f_matching_last : fMiddle lateSwitch = fLate lateSwitch := by
  simp only [fMiddle, fLate, k, lateSwitch_trig]
  linear_combination firstSwitch_eqs.2.1 - firstSwitch_eqs.2.2 / 6

theorem g_matching_last : gMiddle lateSwitch = gLate lateSwitch := by
  simp only [gMiddle, gLate, k, lateSwitch_trig]; linear_combination firstSwitch_eqs.1

theorem fD_matching_last : fMiddleD lateSwitch = fLateD lateSwitch := by
  simp only [fMiddleD, fLateD, k, lateSwitch_trig]; linear_combination -firstSwitch_eqs.1 / 2

theorem gD_matching_last : gMiddleD lateSwitch = gLateD lateSwitch := by
  simp only [gMiddleD, gLateD, k, lateSwitch_trig]
  linear_combination firstSwitch_eqs.2.1 / 2 - firstSwitch_eqs.2.2 / 3

theorem hasDerivAt_referenceF (t : ℝ) : HasDerivAt referenceF (referenceFD t) t :=
  hasDerivAt_joinThree beta_lt_lateSwitch.le
    (fun x => (Real.hasDerivAt_cos x).add ((Real.hasDerivAt_sin x).const_mul (1 / 2)))
    (fun x => ((((hasDerivAt_middlePhaseAngle x).cos.const_mul R).add
      ((Real.hasDerivAt_cos x).const_mul k)).add
      ((Real.hasDerivAt_sin x).const_mul (1 / 2))).congr_deriv (by unfold fMiddleD; ring))
    (fun x => ((((Real.hasDerivAt_cos x).const_mul (1 - 2 / 3 * A)).add
      ((Real.hasDerivAt_sin x).const_mul (1 / 2))).add_const (1 / 2)).congr_deriv
      (by unfold fLateD; ring))
    f_matching_first f_matching_last fD_matching_first fD_matching_last t

theorem hasDerivAt_referenceG (t : ℝ) : HasDerivAt referenceG (referenceGD t) t :=
  hasDerivAt_joinThree beta_lt_lateSwitch.le
    (fun x => ((((Real.hasDerivAt_sin x).const_mul (2 * A - 1)).add
      ((Real.hasDerivAt_cos x).const_mul (1 / 2))).add_const (1 / 2)).congr_deriv
      (by unfold gEarlyD; ring))
    (fun x => ((((hasDerivAt_middlePhaseAngle x).sin.const_mul R).sub
      ((Real.hasDerivAt_sin x).const_mul k)).add
      ((Real.hasDerivAt_cos x).const_mul (1 / 2))).congr_deriv (by unfold gMiddleD; ring))
    (fun x => (((Real.hasDerivAt_sin x).const_mul (8 / 3 * A - 1)).add
      ((Real.hasDerivAt_cos x).const_mul (1 / 2))).congr_deriv (by unfold gLateD; ring))
    g_matching_first g_matching_last gD_matching_first gD_matching_last t

theorem continuous_referenceF : Continuous referenceF :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_referenceF t).continuousAt

theorem continuous_referenceG : Continuous referenceG :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_referenceG t).continuousAt

theorem continuous_referenceFD : Continuous referenceFD :=
  continuous_joinThree beta_lt_lateSwitch.le (by unfold fEarlyD; fun_prop)
    (by unfold fMiddleD; fun_prop) (by unfold fLateD; fun_prop) fD_matching_first
    fD_matching_last

theorem continuous_referenceGD : Continuous referenceGD :=
  continuous_joinThree beta_lt_lateSwitch.le (by unfold gEarlyD; fun_prop)
    (by unfold gMiddleD; fun_prop) (by unfold gLateD; fun_prop) gD_matching_first
    gD_matching_last

theorem referenceF_eq_right_phases (t : ℝ) :
    referenceF t = if t < beta then fEarly t else if t < lateSwitch then fMiddle t else fLate t :=
  phases_eq_right f_matching_first f_matching_last t

theorem referenceG_eq_right_phases (t : ℝ) :
    referenceG t = if t < beta then gEarly t else if t < lateSwitch then gMiddle t else gLate t :=
  phases_eq_right g_matching_first g_matching_last t

theorem referenceF_zero : referenceF 0 = 1 := by
  norm_num [referenceF, fEarly, le_of_lt beta_pos]

theorem referenceG_zero : referenceG 0 = 1 := by
  norm_num [referenceG, gEarly, le_of_lt beta_pos]

theorem referenceF_pi_div_two : referenceF (Real.pi / 2) = 1 := by
  norm_num [referenceF, fLate, not_le.mpr beta_lt_pi_div_two,
    not_le.mpr lateSwitch_lt_pi_div_two]

theorem referenceG_pi_div_two : referenceG (Real.pi / 2) = 8 / 3 * A - 1 := by
  simp [referenceG, gLate, not_le.mpr beta_lt_pi_div_two,
    not_le.mpr lateSwitch_lt_pi_div_two]

theorem referenceFD_zero : referenceFD 0 = 1 / 2 := by simp [referenceFD, fEarlyD, beta_pos.le]

theorem referenceGD_zero : referenceGD 0 = 2 * A - 1 := by
  simp [referenceGD, gEarlyD, beta_pos.le]

theorem referenceFD_pi_div_two : referenceFD (Real.pi / 2) = 2 / 3 * A - 1 := by
  simp [referenceFD, fLateD, not_le.mpr beta_lt_pi_div_two, not_le.mpr lateSwitch_lt_pi_div_two]

theorem referenceGD_pi_div_two : referenceGD (Real.pi / 2) = -(1 / 2) := by
  simp [referenceGD, gLateD, not_le.mpr beta_lt_pi_div_two, not_le.mpr lateSwitch_lt_pi_div_two]

theorem middlePhase_bounds {t : ℝ} (h₁ : beta ≤ t) (h₂ : t ≤ lateSwitch) :
    0 < R * Real.cos (t / 2 + Real.pi / 8) ∧ R * Real.cos (t / 2 + Real.pi / 8) < 7 / 6 ∧
      R * Real.sin (t / 2 + Real.pi / 8) < 7 / 6 := by
  have hb : R * Real.cos (beta / 2 + Real.pi / 8) < 7 / 6 := by
    have h : A * Real.cos beta < 7 / 8 := A_mul_cosBeta_lt_seven_eighths
    rw [firstSwitch_eqs.1]; linarith
  unfold lateSwitch at h₂
  have := beta_pos; have := Real.pi_pos
  refine ⟨mul_pos R_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩),
    (mul_le_mul_of_nonneg_left (Real.cos_le_cos_of_nonneg_of_le_pi (by linarith)
      (by linarith) (by linarith)) R_pos.le).trans_lt hb,
    (mul_le_mul_of_nonneg_left ?_ R_pos.le).trans_lt hb⟩
  rw [← Real.cos_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)

theorem referenceG_complement (t : ℝ) :
    referenceG (Real.pi / 2 - t) = referenceF t - 2 * k * Real.cos t := by

  have h1 : Real.pi / 2 - t < beta ↔ ¬t ≤ lateSwitch := by rw [not_le, sub_lt_comm]; rfl
  have h2 : Real.pi / 2 - t < lateSwitch ↔ ¬t ≤ beta := by
    rw [not_le, sub_lt_comm, lateSwitch, sub_sub_cancel]
  have hu : (Real.pi / 2 - t) / 2 + Real.pi / 8 = Real.pi / 2 - (t / 2 + Real.pi / 8) := by ring
  simp only [referenceG_eq_right_phases, referenceF, h1, h2]
  split_ifs <;> first
    | (exfalso; linarith [beta_lt_lateSwitch])
    | (simp only [gEarly, gMiddle, gLate, fEarly, fMiddle, fLate, k, hu, Real.sin_pi_div_two_sub,
        Real.cos_pi_div_two_sub]; ring)

theorem referenceF_complement (t : ℝ) :
    referenceF (Real.pi / 2 - t) = referenceG t + 2 * k * Real.sin t := by
  have h := referenceG_complement (Real.pi / 2 - t)
  rw [sub_sub_cancel, Real.cos_pi_div_two_sub] at h
  linarith

theorem referenceGD_complement (t : ℝ) :
    referenceGD (Real.pi / 2 - t) = -referenceFD t - 2 * k * Real.sin t := by
  have h := ((hasDerivAt_referenceF t).sub ((Real.hasDerivAt_cos t).const_mul (2 * k)))
  have := ((hasDerivAt_referenceG (Real.pi / 2 - t)).comp t
    ((hasDerivAt_id' t).const_sub _)).unique (h.congr_of_eventuallyEq
      (.of_forall referenceG_complement))
  linarith

theorem referenceF_ge_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    k * Real.cos t + 1 / 2 * Real.sin t ≤ referenceF t := by
  have hc : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hphase : 0 < Real.cos (t / 2 + Real.pi / 8) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  unfold referenceF fEarly fMiddle fLate k
  split_ifs <;> linarith [mul_nonneg A_pos.le hc, mul_pos R_pos hphase]

theorem referenceG_ge_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    -k * Real.sin t + 1 / 2 * Real.cos t ≤ referenceG t := by
  have h := referenceF_ge_center (t := Real.pi / 2 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [referenceF_complement, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at h
  linarith

end AmbidextrousSofa.Reference

end BPn2

end BP2

section BP3

noncomputable section BPn3

namespace AmbidextrousSofa

abbrev Plane := ℝ × ℝ

def rotate (θ : ℝ) (p : Plane) : Plane :=
  (Real.cos θ * p.1 - Real.sin θ * p.2,
    Real.sin θ * p.1 + Real.cos θ * p.2)

def rigidMap (θ : ℝ) (v p : Plane) : Plane := rotate θ p + v

theorem rotate_zero (p : Plane) : rotate 0 p = p := by simp [rotate]

theorem rigidMap_zero_zero (p : Plane) : rigidMap 0 0 p = p := by simp [rigidMap, rotate_zero]

def reflect (p : Plane) : Plane := (p.1, 1 - p.2)

theorem reflect_reflect (p : Plane) : reflect (reflect p) = p := by simp [reflect]

def unitStrip : Set Plane := {p | 0 ≤ p.2 ∧ p.2 ≤ 1}

def incomingArm : Set Plane := {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

def lowerOutgoingArm : Set Plane := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1}

def upperOutgoingArm : Set Plane := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2}

def lowerHall : Set Plane := incomingArm ∪ lowerOutgoingArm

def upperHall : Set Plane := incomingArm ∪ upperOutgoingArm

theorem sin_cos_pos_of_mem_quarter {t : ℝ} (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin t ∧ 0 < Real.cos t :=
  ⟨Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos]),
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩⟩

end AmbidextrousSofa

end BPn3

end BP3

section BP4

namespace AmbidextrousSofa

def horizontalProjection (S : Set Plane) : Set ℝ := Prod.fst '' S

def upperCap (K : Set Plane) : Set Plane :=
  {p | 0 ≤ p.2 ∧ ∃ y : ℝ, p.2 ≤ y ∧ (p.1, y) ∈ K}

structure IsDownwardCap (U : Set Plane) : Prop where
  nonempty : U.Nonempty
  isCompact : IsCompact U
  convex : Convex ℝ U
  inStrip : U ⊆ unitStrip
  downward : ∀ p ∈ U, ∀ y : ℝ, 0 ≤ y → y ≤ p.2 → (p.1, y) ∈ U

theorem upperCap_downward {K : Set Plane} {p : Plane} (hp : p ∈ upperCap K)
    {y : ℝ} (hy0 : 0 ≤ y) (hyp : y ≤ p.2) : (p.1, y) ∈ upperCap K :=
  ⟨hy0, hp.2.imp fun _ h => ⟨hyp.trans h.1, h.2⟩⟩

theorem subset_upperCap {K : Set Plane} (hK : ∀ p ∈ K, 0 ≤ p.2) : K ⊆ upperCap K :=
  fun p hp => ⟨hK p hp, p.2, le_rfl, hp⟩

theorem horizontalProjection_upperCap {K : Set Plane} (hK : ∀ p ∈ K, 0 ≤ p.2) :
    horizontalProjection (upperCap K) = horizontalProjection K :=
  Set.Subset.antisymm (fun _ ⟨_, ⟨_, _, _, hy⟩, hpx⟩ => ⟨_, hy, hpx⟩)
    (Set.image_mono (subset_upperCap hK))

end AmbidextrousSofa

end BP4

section BP5

noncomputable section BPn5

open Set

namespace AmbidextrousSofa

theorem isCompact_upperCap {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) : IsCompact (upperCap K) := by

  have h : upperCap K = (fun z : Plane × ℝ => (z.1.1, z.2 * z.1.2)) '' (K ×ˢ Icc (0 : ℝ) 1) := by
    refine Subset.antisymm ?_ ?_
    · rintro p ⟨hp0, y, hpy, hy⟩
      exact ⟨((p.1, y), p.2 / y), ⟨hy, div_nonneg hp0 (hp0.trans hpy),
        div_le_one_of_le₀ hpy (hp0.trans hpy)⟩,
        Prod.ext rfl (div_mul_cancel_of_imp fun h => le_antisymm (h ▸ hpy) hp0)⟩
    · rintro _ ⟨⟨q, t⟩, ⟨hq, ht⟩, rfl⟩
      exact ⟨mul_nonneg ht.1 (hK0 q hq), q.2, mul_le_of_le_one_left (hK0 q hq) ht.2, hq⟩
  rw [h]
  exact (hK.prod isCompact_Icc).image (by fun_prop)

theorem isDownwardCap_upperCap {K : Set Plane} (hne : K.Nonempty)
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (hstrip : K ⊆ unitStrip) :
    IsDownwardCap (upperCap K) where
  nonempty := hne.mono (subset_upperCap (fun _ hp => (hstrip hp).1))
  isCompact := isCompact_upperCap hcompact (fun _ hp => (hstrip hp).1)
  convex := by
    rintro p ⟨hp0, yp, hpyp, hyp⟩ q ⟨hq0, yq, hqyq, hyq⟩ a b ha hb hab
    exact ⟨add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0), a * yp + b * yq,
      add_le_add (mul_le_mul_of_nonneg_left hpyp ha) (mul_le_mul_of_nonneg_left hqyq hb),
      by simpa [smul_eq_mul] using hconvex hyp hyq ha hb hab⟩
  inStrip := fun _ ⟨hp0, _, hpy, hy⟩ => ⟨hp0, hpy.trans (hstrip hy).2⟩
  downward := fun _ hp _ hy0 hyp => upperCap_downward hp hy0 hyp

theorem isCompact_horizontalProjection {K : Set Plane} (hK : IsCompact K) :
    IsCompact (horizontalProjection K) :=
  hK.image continuous_fst

theorem convex_horizontalProjection {K : Set Plane} (hK : Convex ℝ K) :
    Convex ℝ (horizontalProjection K) := by
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩ a b ha hb hab
  exact ⟨a • p + b • q, hK hp hq ha hb hab, rfl⟩

def horizontalLeft (K : Set Plane) : ℝ := sInf (horizontalProjection K)

def horizontalRight (K : Set Plane) : ℝ := sSup (horizontalProjection K)

theorem horizontalProjection_eq_Icc_of_isConnected {S : Set Plane}
    (hcompact : IsCompact S) (hconnected : IsConnected S) :
    horizontalProjection S = Icc (horizontalLeft S) (horizontalRight S) :=
  eq_Icc_of_connected_compact (hconnected.image Prod.fst continuous_fst.continuousOn)
    (isCompact_horizontalProjection hcompact)

theorem IsDownwardCap.horizontalProjection_eq_Icc {U : Set Plane} (hU : IsDownwardCap U) :
    horizontalProjection U = Icc (horizontalLeft U) (horizontalRight U) :=
  horizontalProjection_eq_Icc_of_isConnected hU.isCompact (hU.convex.isConnected hU.nonempty)

theorem horizontalLeft_mem {K : Set Plane} (hne : K.Nonempty) (hK : IsCompact K) :
    horizontalLeft K ∈ horizontalProjection K :=
  (isCompact_horizontalProjection hK).sInf_mem (hne.image Prod.fst)

theorem horizontalRight_mem {K : Set Plane} (hne : K.Nonempty) (hK : IsCompact K) :
    horizontalRight K ∈ horizontalProjection K :=
  (isCompact_horizontalProjection hK).sSup_mem (hne.image Prod.fst)

theorem horizontalLeft_le_horizontalRight {K : Set Plane} (hne : K.Nonempty)
    (hK : IsCompact K) : horizontalLeft K ≤ horizontalRight K :=
  le_csSup (isCompact_horizontalProjection hK).bddAbove (horizontalLeft_mem hne hK)

def verticalFiber (K : Set Plane) (x : ℝ) : Set ℝ := {y | (x, y) ∈ K}

theorem verticalFiber_nonempty_iff {K : Set Plane} {x : ℝ} :
    (verticalFiber K x).Nonempty ↔ x ∈ horizontalProjection K :=
  ⟨fun ⟨y, hy⟩ => ⟨(x, y), hy, rfl⟩, by rintro ⟨p, hp, rfl⟩; exact ⟨p.2, hp⟩⟩

theorem isCompact_verticalFiber {K : Set Plane} (hK : IsCompact K) (x : ℝ) :
    IsCompact (verticalFiber K x) := by
  convert (hK.inter_right (isClosed_eq continuous_fst continuous_const)).image continuous_snd
  ext y
  exact ⟨fun hy => ⟨(x, y), ⟨hy, rfl⟩, rfl⟩, by rintro ⟨p, ⟨hp, rfl⟩, rfl⟩; exact hp⟩

def capRoof (K : Set Plane) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ horizontalProjection K then sSup (verticalFiber K x) else 0

theorem capRoof_eq_zero_of_not_mem {K : Set Plane} {x : ℝ}
    (hx : x ∉ horizontalProjection K) : capRoof K x = 0 := by
  simp only [capRoof, hx, ↓reduceIte]

theorem capRoof_mem {K : Set Plane} (hK : IsCompact K) {x : ℝ}
    (hx : x ∈ horizontalProjection K) : (x, capRoof K x) ∈ K := by
  simpa only [capRoof, hx, ↓reduceIte, verticalFiber, Set.mem_ofPred_eq] using
    (isCompact_verticalFiber hK x).sSup_mem (verticalFiber_nonempty_iff.mpr hx)

theorem le_capRoof {K : Set Plane} (hK : IsCompact K) {x y : ℝ}
    (hxy : (x, y) ∈ K) : y ≤ capRoof K x := by
  simpa only [capRoof, show x ∈ horizontalProjection K from ⟨(x, y), hxy, rfl⟩, ↓reduceIte] using
    le_csSup (isCompact_verticalFiber hK x).bddAbove hxy

theorem capRoof_nonneg {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) (x : ℝ) : 0 ≤ capRoof K x := by
  by_cases hx : x ∈ horizontalProjection K
  exacts [hK0 _ (capRoof_mem hK hx), (capRoof_eq_zero_of_not_mem hx).ge]

theorem capRoof_le_one {K : Set Plane} (hK : IsCompact K) (hstrip : K ⊆ unitStrip)
    (x : ℝ) : capRoof K x ≤ 1 := by
  by_cases hx : x ∈ horizontalProjection K
  exacts [(hstrip (capRoof_mem hK hx)).2, (capRoof_eq_zero_of_not_mem hx).trans_le zero_le_one]

theorem IsDownwardCap.concaveOn_capRoof {U : Set Plane} (hU : IsDownwardCap U) :
    ConcaveOn ℝ (horizontalProjection U) (capRoof U) := by
  refine ⟨convex_horizontalProjection hU.convex, fun x hx y hy a b ha hb hab =>
    le_capRoof hU.isCompact ?_⟩
  simpa [smul_eq_mul] using hU.convex (capRoof_mem hU.isCompact hx) (capRoof_mem hU.isCompact hy)
    ha hb hab

theorem IsDownwardCap.mem_iff_projection_and_roof {U : Set Plane}
    (hU : IsDownwardCap U) (p : Plane) :
    p ∈ U ↔ p.1 ∈ horizontalProjection U ∧ 0 ≤ p.2 ∧ p.2 ≤ capRoof U p.1 :=
  ⟨fun hp => ⟨⟨p, hp, rfl⟩, (hU.inStrip hp).1, le_capRoof hU.isCompact hp⟩,
    fun ⟨hx, hy0, hyroof⟩ => hU.downward _ (capRoof_mem hU.isCompact hx) p.2 hy0 hyroof⟩

theorem capRoof_upperCap {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) (x : ℝ) : capRoof (upperCap K) x = capRoof K x := by
  have hcompact := isCompact_upperCap hK hK0
  by_cases hx : x ∈ horizontalProjection K
  · obtain ⟨_, y, hroofy, hy⟩ :=
      capRoof_mem hcompact (by rwa [horizontalProjection_upperCap hK0] : x ∈ _)
    exact le_antisymm (hroofy.trans (le_capRoof hK hy))
      (le_capRoof hcompact (subset_upperCap hK0 (capRoof_mem hK hx)))
  · rw [capRoof_eq_zero_of_not_mem hx,
      capRoof_eq_zero_of_not_mem (by rwa [horizontalProjection_upperCap hK0])]

theorem upperSemicontinuous_capRoof {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) : UpperSemicontinuous (capRoof K) := by
  refine upperSemicontinuous_iff_isClosed_preimage.mpr fun c => ?_
  by_cases hc : c ≤ 0
  · convert isClosed_univ
    exact eq_univ_of_forall fun x => hc.trans (capRoof_nonneg hK hK0 x)

  convert (isCompact_horizontalProjection
    (hK.inter_right (isClosed_le continuous_const continuous_snd))).isClosed
  refine Subset.antisymm (fun x hx => ?_) ?_
  · have hxK : x ∈ horizontalProjection K := by
      by_contra h
      exact hc (capRoof_eq_zero_of_not_mem h ▸ hx)
    exact ⟨_, ⟨capRoof_mem hK hxK, hx⟩, rfl⟩
  · rintro _ ⟨p, ⟨hp, hcp⟩, rfl⟩
    exact hcp.trans (le_capRoof hK hp)

theorem measurable_capRoof {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) : Measurable (capRoof K) :=
  (upperSemicontinuous_capRoof hK hK0).measurable

theorem IsDownwardCap.upperSemicontinuous_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) : UpperSemicontinuous (capRoof U) :=
  AmbidextrousSofa.upperSemicontinuous_capRoof hU.isCompact (fun _ hp => (hU.inStrip hp).1)

theorem IsDownwardCap.measurable_capRoof {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (capRoof U) :=
  hU.upperSemicontinuous_capRoof.measurable

end AmbidextrousSofa

end BPn5

end BP5

section BP6

noncomputable section BPn6

open Set

namespace AmbidextrousSofa

def coordDot (p v : Plane) : ℝ := p.1 * v.1 + p.2 * v.2

theorem coordDot_add_left (p q v : Plane) : coordDot (p + q) v = coordDot p v + coordDot q v := by
  simp only [coordDot, Prod.fst_add, Prod.snd_add]; ring

theorem coordDot_smul_left (a : ℝ) (p v : Plane) : coordDot (a • p) v = a * coordDot p v := by
  simp only [coordDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem continuous_coordDot_right (v : Plane) : Continuous (fun p => coordDot p v) := by
  unfold coordDot; fun_prop

def support (K : Set Plane) (v : Plane) : ℝ := sSup ((fun p => coordDot p v) '' K)

def unitNormal (θ : ℝ) : Plane := (Real.cos θ, Real.sin θ)

def angleSupport (K : Set Plane) (θ : ℝ) : ℝ := support K (unitNormal θ)

theorem support_bddAbove {K : Set Plane} (hK : IsCompact K) (v : Plane) :
    BddAbove ((fun p => coordDot p v) '' K) :=
  hK.bddAbove_image (continuous_coordDot_right v).continuousOn

theorem coordDot_le_support {K : Set Plane} (hK : IsCompact K) {p : Plane}
    (hp : p ∈ K) (v : Plane) : coordDot p v ≤ support K v :=
  le_csSup (support_bddAbove hK v) (mem_image_of_mem _ hp)

theorem support_le_of_forall {K : Set Plane} (hne : K.Nonempty) {v : Plane} {c : ℝ}
    (h : ∀ p ∈ K, coordDot p v ≤ c) : support K v ≤ c :=
  csSup_le (hne.image _) (forall_mem_image.2 h)

theorem support_mono {K L : Set Plane} (hKL : K ⊆ L) (hne : K.Nonempty)
    (hL : IsCompact L) (v : Plane) : support K v ≤ support L v :=
  csSup_le_csSup (support_bddAbove hL v) (hne.image _) (image_mono hKL)

theorem support_eq_of_mem {K : Set Plane} (hK : IsCompact K) {v : Plane} {c : ℝ}
    (hle : ∀ p ∈ K, coordDot p v ≤ c) {q : Plane} (hq : q ∈ K)
    (hqc : coordDot q v = c) : support K v = c :=
  (support_le_of_forall ⟨q, hq⟩ hle).antisymm (hqc ▸ coordDot_le_support hK hq v)

theorem continuous_support {K : Set Plane} (hK : IsCompact K) : Continuous (support K) :=
  hK.continuous_sSup (f := fun v p => coordDot p v) (by unfold coordDot; fun_prop)

theorem continuous_unitNormal : Continuous unitNormal := by unfold unitNormal; fun_prop

theorem convex_coordDot_halfspace (v : Plane) (c : ℝ) :
    Convex ℝ {p : Plane | coordDot p v ≤ c} :=
  convex_halfSpace_le ⟨fun p q => coordDot_add_left p q v, fun a p => coordDot_smul_left a p v⟩ c

theorem support_upperCap {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) {v : Plane} (hv : 0 ≤ v.2) :
    support (upperCap K) v = support K v := by
  refine le_antisymm (support_le_of_forall (hne.mono (subset_upperCap hK0)) ?_)
    (support_mono (subset_upperCap hK0) hne (isCompact_upperCap hK hK0) v)
  rintro p ⟨-, y, hpy, hy⟩
  exact (show coordDot p v ≤ coordDot (p.1, y) v from
    add_le_add_right (mul_le_mul_of_nonneg_right hpy hv) _).trans (coordDot_le_support hK hy v)

theorem angleSupport_upperCap {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) {θ : ℝ} (hθ : 0 ≤ Real.sin θ) :
    angleSupport (upperCap K) θ = angleSupport K θ :=
  support_upperCap hK hne hK0 hθ

theorem coordDot_rotate (θ : ℝ) (p v : Plane) :
    coordDot (rotate θ p) v = coordDot p (rotate (-θ) v) := by
  simp only [coordDot, rotate, Real.cos_neg, Real.sin_neg]; ring

theorem rotate_unitNormal (θ φ : ℝ) : rotate θ (unitNormal φ) = unitNormal (θ + φ) := by
  simp only [rotate, unitNormal, Real.cos_add, Real.sin_add]

theorem support_horizontal_right (K : Set Plane) : support K (1, 0) = horizontalRight K := by
  simp only [support, coordDot, mul_one, mul_zero, add_zero, horizontalRight, horizontalProjection]

theorem support_horizontal_left {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty) :
    support K (-1, 0) = -horizontalLeft K := by
  obtain ⟨p, hp, hpLeft⟩ := horizontalLeft_mem hne hK
  refine support_eq_of_mem hK (fun q hq => ?_) hp
    (by simp only [coordDot, mul_neg, mul_one, mul_zero, add_zero, hpLeft])
  simp only [coordDot, mul_neg, mul_one, mul_zero, add_zero, neg_le_neg_iff]
  exact csInf_le (isCompact_horizontalProjection hK).bddBelow (mem_image_of_mem Prod.fst hq)

end AmbidextrousSofa

end BPn6

end BP6

section BP7

noncomputable section BPn7

open Set

namespace AmbidextrousSofa

end AmbidextrousSofa

end BPn7

end BP7

section BP8

noncomputable section BPn8

namespace AmbidextrousSofa

def motionInterval : Set ℝ := Set.Icc 0 1

structure RigidMotionPath where
  angle : ℝ → ℝ
  shift : ℝ → Plane
  continuous_angle : ContinuousOn angle motionInterval
  continuous_shift : ContinuousOn shift motionInterval

def RigidMotionPath.placement (path : RigidMotionPath) (t : ℝ) : Plane → Plane :=
  rigidMap (path.angle t) (path.shift t)

structure Passage (S hall incoming outgoing : Set Plane) (path : RigidMotionPath) : Prop where
  inside : ∀ t ∈ motionInterval, path.placement t '' S ⊆ hall
  start : path.placement 0 '' S ⊆ incoming
  finish : path.placement 1 '' S ⊆ outgoing

def SameInitialOrientation (lower upper : RigidMotionPath) : Prop :=
  rotate (lower.angle 0) = rotate (upper.angle 0)

structure IsAmbidextrous (S : Set Plane) : Prop where
  nonempty : S.Nonempty
  isCompact : IsCompact S
  isConnected : IsConnected S
  passages : ∃ lower upper : RigidMotionPath,
    SameInitialOrientation lower upper ∧
      Passage S lowerHall incomingArm lowerOutgoingArm lower ∧
      Passage S upperHall incomingArm upperOutgoingArm upper

end AmbidextrousSofa

end BPn8

end BP8

section BP9

noncomputable section BPn9

open Set

namespace AmbidextrousSofa

theorem continuous_reflect : Continuous reflect := by unfold reflect; fun_prop

theorem mem_image_reflect (K : Set Plane) (p : Plane) : p ∈ reflect '' K ↔ reflect p ∈ K :=
  mem_image_iff_of_inverse reflect_reflect reflect_reflect

theorem image_reflect_eq_preimage (K : Set Plane) : reflect '' K = reflect ⁻¹' K :=
  ext (mem_image_reflect K)

def reflectAffineMap : Plane →ᵃ[ℝ] Plane where
  toFun := reflect
  linear := LinearMap.prodMap LinearMap.id (-LinearMap.id)
  map_vadd' _ _ := Prod.ext rfl (by simp [reflect]; ring)

theorem convex_preimage_reflect {K : Set Plane} (hK : Convex ℝ K) : Convex ℝ (reflect ⁻¹' K) :=
  hK.affine_preimage reflectAffineMap

theorem convex_verticalFiber {K : Set Plane} (hK : Convex ℝ K) (x : ℝ) :
    Convex ℝ (verticalFiber K x) := fun y hy z hz a b ha hb hab => by
  simpa [verticalFiber, ← add_mul, hab] using hK hy hz ha hb hab

end AmbidextrousSofa

end BPn9

end BP9

section BP10

noncomputable section BPn10

open Set

namespace AmbidextrousSofa.Reference

def center : Plane := (k, 1 / 2)

def upperHalfPlanes (t : ℝ) : Set Plane :=
  {p | coordDot p (unitNormal t) ≤ referenceF t ∧
    coordDot p (unitNormal (t + Real.pi / 2)) ≤ referenceG t}

def referenceHull : Set Plane :=
  ⋂ t ∈ Icc (0 : ℝ) (Real.pi / 2),
    upperHalfPlanes t ∩ reflect ⁻¹' upperHalfPlanes t

def referenceBox : Set Plane :=
  Icc (1 - 8 / 3 * A) 1 ×ˢ Icc (0 : ℝ) 1

def referenceCap : Set Plane := upperCap referenceHull

theorem mem_referenceHull_iff (p : Plane) :
    p ∈ referenceHull ↔ ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      p ∈ upperHalfPlanes t ∧ reflect p ∈ upperHalfPlanes t := by
  simp only [referenceHull, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]

theorem center_mem_referenceHull : center ∈ referenceHull := by
  have hc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : center ∈ upperHalfPlanes t := by
    refine ⟨referenceF_ge_center ht, ?_⟩
    simpa only [coordDot, center, unitNormal, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
      mul_neg, neg_mul] using referenceG_ge_center ht
  have hr : reflect center = center := by norm_num [reflect, center]
  exact (mem_referenceHull_iff center).2 fun t ht => ⟨hc ht, by rw [hr]; exact hc ht⟩

theorem referenceHull_nonempty : referenceHull.Nonempty :=
  ⟨center, center_mem_referenceHull⟩

theorem isClosed_referenceHull : IsClosed referenceHull := by
  have h (t : ℝ) : IsClosed (upperHalfPlanes t) :=
    (isClosed_le (continuous_coordDot_right _) continuous_const).inter
      (isClosed_le (continuous_coordDot_right _) continuous_const)
  exact isClosed_biInter fun t _ => (h t).inter ((h t).preimage continuous_reflect)

theorem convex_referenceHull : Convex ℝ referenceHull := by
  have h (t : ℝ) : Convex ℝ (upperHalfPlanes t) :=
    (convex_coordDot_halfspace _ _).inter (convex_coordDot_halfspace _ _)
  exact convex_iInter₂ fun t _ => (h t).inter (convex_preimage_reflect (h t))

theorem referenceHull_subset_box : referenceHull ⊆ referenceBox := fun p hp => by
  have h0 := (mem_referenceHull_iff p).1 hp 0 ⟨le_rfl, by positivity⟩
  have h1 := ((mem_referenceHull_iff p).1 hp (Real.pi / 2) ⟨by positivity, le_rfl⟩).1.2
  simp only [upperHalfPlanes, mem_ofPred_eq, coordDot, unitNormal, reflect, zero_add, add_halves,
    Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_pi,
    Real.sin_pi, mul_one, mul_zero, add_zero, mul_neg, referenceF_zero, referenceG_zero,
    referenceG_pi_div_two] at h0 h1
  exact ⟨⟨by linarith, h0.1.1⟩, by linarith, h0.1.2⟩

theorem referenceHull_subset_unitStrip : referenceHull ⊆ unitStrip :=
  fun _ hp => (referenceHull_subset_box hp).2

theorem isCompact_referenceHull : IsCompact referenceHull :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_referenceHull
    referenceHull_subset_box

theorem reflect_mem_referenceHull (p : Plane) :
    reflect p ∈ referenceHull ↔ p ∈ referenceHull := by
  simp only [mem_referenceHull_iff, reflect_reflect, and_comm]

theorem isDownwardCap_referenceCap : IsDownwardCap referenceCap :=
  isDownwardCap_upperCap referenceHull_nonempty isCompact_referenceHull
    convex_referenceHull referenceHull_subset_unitStrip

theorem referenceHull_subset_referenceCap : referenceHull ⊆ referenceCap :=
  subset_upperCap (fun _ hp => (referenceHull_subset_unitStrip hp).1)

theorem horizontalProjection_referenceCap :
    horizontalProjection referenceCap = horizontalProjection referenceHull :=
  horizontalProjection_upperCap (fun _ hp => (referenceHull_subset_unitStrip hp).1)

theorem angleSupport_referenceCap {t : ℝ} (ht : 0 ≤ Real.sin t) :
    angleSupport referenceCap t = angleSupport referenceHull t :=
  angleSupport_upperCap isCompact_referenceHull referenceHull_nonempty
    (fun _ hp => (referenceHull_subset_unitStrip hp).1) ht

end AmbidextrousSofa.Reference

end BPn10

end BP10

section BP11

noncomputable section BPn11

open Set
open scoped Topology

namespace AmbidextrousSofa.Reference

def supportPoint (h hD : ℝ → ℝ) (t : ℝ) : Plane :=
  (h t * Real.cos t - hD t * Real.sin t,
    h t * Real.sin t + hD t * Real.cos t)

def companionSupportPoint (h hD : ℝ → ℝ) (t : ℝ) : Plane :=
  rotate (Real.pi / 2) (supportPoint h hD t)

def supportProjection (h hD : ℝ → ℝ) (φ t : ℝ) : ℝ :=
  h t * Real.cos (φ - t) + hD t * Real.sin (φ - t)

theorem coordDot_supportPoint (h hD : ℝ → ℝ) (φ t : ℝ) :
    coordDot (supportPoint h hD t) (unitNormal φ) = supportProjection h hD φ t := by
  simp only [coordDot, supportPoint, unitNormal, supportProjection, Real.cos_sub, Real.sin_sub]
  ring

theorem coordDot_companionSupportPoint (h hD : ℝ → ℝ) (φ t : ℝ) :
    coordDot (companionSupportPoint h hD t) (unitNormal φ) =
      supportProjection h hD (φ - Real.pi / 2) t := by
  rw [companionSupportPoint, coordDot_rotate, rotate_unitNormal, neg_add_eq_sub,
    coordDot_supportPoint]

theorem supportProjection_self (h hD : ℝ → ℝ) (t : ℝ) :
    supportProjection h hD t t = h t := by
  simp [supportProjection]

theorem hasDerivWithinAt_phases_right {p q r pD qD rD : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p (pD x) x) (hq : ∀ x, HasDerivAt q (qD x) x)
    (hr : ∀ x, HasDerivAt r (rD x) x) (h₁ : p beta = q beta)
    (h₂ : q lateSwitch = r lateSwitch) (t : ℝ) :
    HasDerivWithinAt (fun t => if t ≤ beta then p t else if t ≤ lateSwitch then q t else r t)
      (if t < beta then pD t else if t < lateSwitch then qD t else rD t) (Ioi t) t := by
  simp only [phases_eq_right h₁ h₂]
  split_ifs with ha hb
  · refine (hp t).hasDerivWithinAt.congr_of_eventuallyEq ?_ (ite_eq_left ha)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds ha)] with s hs
    rw [ite_eq_left hs]
  · refine (hq t).hasDerivWithinAt.congr_of_eventuallyEq ?_
      (by rw [ite_eq_right ha, ite_eq_left hb])
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds hb)]
      with s hs hs'
    rw [ite_eq_right fun h => ha (hs.out.trans h), ite_eq_left hs']
  · refine (hr t).hasDerivWithinAt.congr_of_eventuallyEq ?_
      (by rw [ite_eq_right ha, ite_eq_right hb])
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [ite_eq_right fun h => ha (hs.out.trans h), ite_eq_right fun h => hb (hs.out.trans h)]

theorem hasDerivWithinAt_supportProjection {h hD : ℝ → ℝ} {hDD φ t : ℝ}
    (hh : HasDerivWithinAt h (hD t) (Ioi t) t)
    (hhD : HasDerivWithinAt hD hDD (Ioi t) t) :
    HasDerivWithinAt (supportProjection h hD φ)
      ((h t + hDD) * Real.sin (φ - t)) (Ioi t) t := by
  have hangle := (hasDerivAt_id' t).const_sub φ
  exact ((hh.mul hangle.cos.hasDerivWithinAt).add
    (hhD.mul hangle.sin.hasDerivWithinAt)).congr_deriv (by ring)

theorem supportProjection_le_of_le {h hD hDD : ℝ → ℝ} {a b φ : ℝ}
    (hh : Continuous h) (hhD : Continuous hD)
    (hderiv : ∀ x, HasDerivWithinAt h (hD x) (Ioi x) x)
    (hsecond : ∀ x, HasDerivWithinAt hD (hDD x) (Ioi x) x)
    (hcurv : ∀ x ∈ Icc a b, 0 ≤ h x + hDD x)
    (hab : a ≤ b) (hbφ : b ≤ φ) (hφa : φ - a ≤ Real.pi) :
    supportProjection h hD φ a ≤ supportProjection h hD φ b := by

  simpa only [intervalIntegral.integral_zero, sub_nonneg] using
    intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab
      (Continuous.continuousOn (by unfold supportProjection; fun_prop))
      (fun x _ => hasDerivWithinAt_supportProjection (hderiv x) (hsecond x)) (φ := fun _ => 0)
      (by simp) fun x hx => mul_nonneg (hcurv x ⟨hx.1.le, hx.2.le⟩)
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.2]) (by linarith [hx.1]))

theorem supportProjection_le_of_ge {h hD hDD : ℝ → ℝ} {a b φ : ℝ}
    (hh : Continuous h) (hhD : Continuous hD)
    (hderiv : ∀ x, HasDerivWithinAt h (hD x) (Ioi x) x)
    (hsecond : ∀ x, HasDerivWithinAt hD (hDD x) (Ioi x) x)
    (hcurv : ∀ x ∈ Icc a b, 0 ≤ h x + hDD x)
    (hab : a ≤ b) (hφa : φ ≤ a) (hbφ : b - φ ≤ Real.pi) :
    supportProjection h hD φ b ≤ supportProjection h hD φ a := by
  have key := supportProjection_le_of_le hh hhD hderiv hsecond hcurv hab (φ := φ + Real.pi)
    (by linarith) (by linarith)
  simp only [supportProjection, add_sub_right_comm, Real.cos_add_pi, Real.sin_add_pi] at key ⊢
  linarith

theorem supportProjection_le_self {h hD hDD : ℝ → ℝ} {a b s t : ℝ}
    (hh : Continuous h) (hhD : Continuous hD)
    (hderiv : ∀ x, HasDerivWithinAt h (hD x) (Ioi x) x)
    (hsecond : ∀ x, HasDerivWithinAt hD (hDD x) (Ioi x) x)
    (hcurv : ∀ x ∈ Icc a b, 0 ≤ h x + hDD x)
    (hwidth : b - a ≤ Real.pi) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    supportProjection h hD t s ≤ h t := by
  rw [← supportProjection_self h hD t]
  rcases le_total s t with hst | hts
  · exact supportProjection_le_of_le hh hhD hderiv hsecond
      (fun x hx => hcurv x ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩) hst le_rfl
      (by linarith [hs.1, ht.2])
  · exact supportProjection_le_of_ge hh hhD hderiv hsecond
      (fun x hx => hcurv x ⟨ht.1.trans hx.1, hx.2.trans hs.2⟩) hts le_rfl
      (by linarith [ht.1, hs.2])

def referenceFSecond (t : ℝ) : ℝ :=
  if t < beta then -Real.cos t - 1 / 2 * Real.sin t
  else if t < lateSwitch then
    -(R / 4) * Real.cos (t / 2 + Real.pi / 8) - k * Real.cos t - 1 / 2 * Real.sin t
  else -(1 - 2 / 3 * A) * Real.cos t - 1 / 2 * Real.sin t

def referenceGSecond (t : ℝ) : ℝ :=
  if t < beta then -(2 * A - 1) * Real.sin t - 1 / 2 * Real.cos t
  else if t < lateSwitch then
    -(R / 4) * Real.sin (t / 2 + Real.pi / 8) + k * Real.sin t - 1 / 2 * Real.cos t
  else -(8 / 3 * A - 1) * Real.sin t - 1 / 2 * Real.cos t

theorem hasDerivWithinAt_referenceFD_right :
    ∀ t, HasDerivWithinAt referenceFD (referenceFSecond t) (Ioi t) t := by
  refine hasDerivWithinAt_phases_right (fun x => ?_) (fun x => ?_) (fun x => ?_)
    fD_matching_first fD_matching_last
  · exact ((Real.hasDerivAt_sin x).neg.add
      ((Real.hasDerivAt_cos x).const_mul (1 / 2))).congr_deriv (by ring)
  · exact ((((hasDerivAt_middlePhaseAngle x).sin.const_mul (-(R / 2))).sub
      ((Real.hasDerivAt_sin x).const_mul k)).add
      ((Real.hasDerivAt_cos x).const_mul (1 / 2))).congr_deriv (by ring)
  · exact (((Real.hasDerivAt_sin x).const_mul (-(1 - 2 / 3 * A))).add
      ((Real.hasDerivAt_cos x).const_mul (1 / 2))).congr_deriv (by ring)

theorem hasDerivWithinAt_referenceGD_right :
    ∀ t, HasDerivWithinAt referenceGD (referenceGSecond t) (Ioi t) t := by
  refine hasDerivWithinAt_phases_right (fun x => ?_) (fun x => ?_) (fun x => ?_)
    gD_matching_first gD_matching_last
  · exact (((Real.hasDerivAt_cos x).const_mul (2 * A - 1)).sub
      ((Real.hasDerivAt_sin x).const_mul (1 / 2))).congr_deriv (by ring)
  · exact ((((hasDerivAt_middlePhaseAngle x).cos.const_mul (R / 2)).sub
      ((Real.hasDerivAt_cos x).const_mul k)).sub
      ((Real.hasDerivAt_sin x).const_mul (1 / 2))).congr_deriv (by ring)
  · exact (((Real.hasDerivAt_cos x).const_mul (8 / 3 * A - 1)).sub
      ((Real.hasDerivAt_sin x).const_mul (1 / 2))).congr_deriv (by ring)

theorem referenceF_right_curvature (t : ℝ) :
    0 ≤ referenceF t + referenceFSecond t ∧ referenceF t + referenceFSecond t < 1 := by
  rw [referenceF_eq_right_phases, referenceFSecond]
  split_ifs with h₁ h₂
  · simp only [fEarly]; ring_nf; norm_num
  · obtain ⟨h₃, h₄, -⟩ := middlePhase_bounds (not_lt.1 h₁) h₂.le
    simp only [fMiddle]; constructor <;> linarith
  · simp only [fLate]; ring_nf; norm_num

theorem referenceG_right_curvature_le_one (t : ℝ) : referenceG t + referenceGSecond t ≤ 1 := by
  rw [referenceG_eq_right_phases, referenceGSecond]
  split_ifs with h₁ h₂
  · simp only [gEarly]; ring_nf; norm_num
  · have := (middlePhase_bounds (not_lt.1 h₁) h₂.le).2.2
    simp only [gMiddle]; linarith
  · simp only [gLate]; ring_nf; norm_num

def fBoundary (t : ℝ) : Plane := supportPoint referenceF referenceFD t

def gBoundary (t : ℝ) : Plane := companionSupportPoint referenceG referenceGD t

theorem coordDot_fBoundary (φ t : ℝ) :
    coordDot (fBoundary t) (unitNormal φ) = supportProjection referenceF referenceFD φ t :=
  coordDot_supportPoint referenceF referenceFD φ t

theorem coordDot_fBoundary_self (t : ℝ) :
    coordDot (fBoundary t) (unitNormal t) = referenceF t := by
  rw [coordDot_fBoundary, supportProjection_self]

theorem coordDot_gBoundary_self (t : ℝ) :
    coordDot (gBoundary t) (unitNormal (t + Real.pi / 2)) = referenceG t := by
  rw [gBoundary, coordDot_companionSupportPoint, add_sub_cancel_right, supportProjection_self]

theorem fBoundary_pi_div_two : fBoundary (Real.pi / 2) = (1 - 2 / 3 * A, 1) := by
  simp [fBoundary, supportPoint, referenceF_pi_div_two, referenceFD_pi_div_two]

theorem mirror_mem_upperHalfPlanes {p : Plane} {t : ℝ} :
    (2 * k - p.1, p.2) ∈ upperHalfPlanes t ↔ p ∈ upperHalfPlanes (Real.pi / 2 - t) := by
  simp only [upperHalfPlanes, mem_ofPred_eq, coordDot, unitNormal, Real.cos_add_pi_div_two,
    Real.sin_add_pi_div_two, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub,
    referenceF_complement, referenceG_complement]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem mirror_mem_referenceHull (p : Plane) :
    (2 * k - p.1, p.2) ∈ referenceHull ↔ p ∈ referenceHull := by
  have key (q : Plane) (hq : q ∈ referenceHull) : (2 * k - q.1, q.2) ∈ referenceHull := by
    refine (mem_referenceHull_iff _).2 fun t ht => ?_
    obtain ⟨h₁, h₂⟩ := (mem_referenceHull_iff q).1 hq (Real.pi / 2 - t)
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact ⟨mirror_mem_upperHalfPlanes.2 h₁, mirror_mem_upperHalfPlanes.2 h₂⟩
  exact ⟨fun h => by simpa using key _ h, key p⟩

theorem gBoundary_eq_mirror (t : ℝ) :
    gBoundary t = (2 * k - (fBoundary (Real.pi / 2 - t)).1, (fBoundary (Real.pi / 2 - t)).2) := by
  have hG := referenceG_complement (Real.pi / 2 - t)
  have hGD := referenceGD_complement (Real.pi / 2 - t)
  rw [sub_sub_cancel, Real.cos_pi_div_two_sub] at hG
  rw [sub_sub_cancel, Real.sin_pi_div_two_sub] at hGD
  simp only [gBoundary, fBoundary, companionSupportPoint, supportPoint, rotate, hG, hGD,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ext <;> [linear_combination 2 * k * Real.sin_sq_add_cos_sq t; ring]

theorem fBoundary_below_first_support {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (Real.pi / 2)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    coordDot (fBoundary s) (unitNormal t) ≤ referenceF t := by
  rw [coordDot_fBoundary]
  exact supportProjection_le_self continuous_referenceF continuous_referenceFD
    (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt)
    hasDerivWithinAt_referenceFD_right (fun x _ => (referenceF_right_curvature x).1)
    (by linarith [Real.pi_pos]) hs ht

theorem fBoundary_above_midline {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : 1 / 2 ≤ (fBoundary t).2 := by
  have h := supportProjection_le_of_le continuous_referenceF continuous_referenceFD
    (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt) hasDerivWithinAt_referenceFD_right
    (fun x _ => (referenceF_right_curvature x).1) ht.1 ht.2 (by linarith [Real.pi_pos])
  rw [← coordDot_fBoundary, ← coordDot_fBoundary, show fBoundary 0 = (1, 1 / 2) by
    simp [fBoundary, supportPoint, referenceF_zero, referenceFD_zero]] at h
  simpa [coordDot, unitNormal] using h

theorem fBoundary_below_companion_support {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (Real.pi / 2)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    coordDot (fBoundary s) (unitNormal (t + Real.pi / 2)) ≤ referenceG t := by

  have h := fBoundary_below_first_support (s := Real.pi / 2) ⟨by positivity, le_rfl⟩
    (t := Real.pi / 2 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [fBoundary_pi_div_two, referenceF_complement] at h
  rw [coordDot_fBoundary]
  refine (supportProjection_le_of_le continuous_referenceF continuous_referenceFD
    (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt) hasDerivWithinAt_referenceFD_right
    (fun x _ => (referenceF_right_curvature x).1) hs.2 (by linarith [ht.1])
    (by linarith [ht.2, hs.1])).trans ?_
  rw [← coordDot_fBoundary, fBoundary_pi_div_two]
  simp only [coordDot, unitNormal, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, k] at h ⊢
  linarith [mul_nonneg A_pos.le
    (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, Real.pi_pos]))]

private theorem mem_referenceHull_of_upper {p : Plane} (hp : 1 / 2 ≤ p.2)
    (h : ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2), p ∈ upperHalfPlanes s) : p ∈ referenceHull := by
  refine (mem_referenceHull_iff p).2 fun s hs => ⟨h s hs, ?_⟩
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2, Real.pi_pos])
  have hcos := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
  obtain ⟨h1, h2⟩ := h s hs
  simp only [upperHalfPlanes, mem_ofPred_eq, coordDot, reflect, unitNormal,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] at h1 h2 ⊢
  constructor <;> linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * p.2 - 1) hsin,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * p.2 - 1) hcos]

theorem fBoundary_mem_referenceHull {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : fBoundary t ∈ referenceHull :=
  mem_referenceHull_of_upper (fBoundary_above_midline ht) fun _ hs =>
    ⟨fBoundary_below_first_support ht hs, fBoundary_below_companion_support ht hs⟩

theorem gBoundary_mem_referenceHull {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : gBoundary t ∈ referenceHull := by
  rw [gBoundary_eq_mirror, mirror_mem_referenceHull]
  exact fBoundary_mem_referenceHull ⟨by linarith [ht.2], by linarith [ht.1]⟩

theorem angleSupport_referenceHull_eq_f {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceHull t = referenceF t :=
  support_eq_of_mem isCompact_referenceHull (fun p hp => ((mem_referenceHull_iff p).1 hp t ht).1.1)
    (fBoundary_mem_referenceHull ht) (coordDot_fBoundary_self t)

theorem angleSupport_referenceHull_eq_g {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceHull (t + Real.pi / 2) = referenceG t :=
  support_eq_of_mem isCompact_referenceHull (fun p hp => ((mem_referenceHull_iff p).1 hp t ht).1.2)
    (gBoundary_mem_referenceHull ht) (coordDot_gBoundary_self t)

theorem angleSupport_referenceCap_eq_f {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceCap t = referenceF t :=
  (angleSupport_referenceCap (Real.sin_nonneg_of_nonneg_of_le_pi ht.1
    (by linarith [ht.2, Real.pi_pos]))).trans (angleSupport_referenceHull_eq_f ht)

theorem angleSupport_referenceCap_eq_g {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceCap (t + Real.pi / 2) = referenceG t :=
  (angleSupport_referenceCap (t := t + Real.pi / 2) (Real.sin_add_pi_div_two t ▸
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)).trans
    (angleSupport_referenceHull_eq_g ht)

end AmbidextrousSofa.Reference

end BPn11

end BP11

section BP12

noncomputable section BPn12

open Set

namespace AmbidextrousSofa.Reference

def momentP (t : ℝ) : ℝ := referenceFD t - referenceG t + 1

def momentQ (t : ℝ) : ℝ := referenceGD t + referenceF t - 1

theorem momentP_phases (t : ℝ) :
    momentP t = if t ≤ beta then 1 / 2 - 2 * A * Real.sin t
      else if t ≤ lateSwitch then 1 - 3 / 2 * R * Real.sin (t / 2 + Real.pi / 8)
      else 1 - 2 * A * Real.sin t := by
  unfold momentP referenceFD referenceG
  split_ifs <;> simp only [fEarlyD, gEarly, fMiddleD, gMiddle, fLateD, gLate] <;> ring

theorem momentQ_complement (t : ℝ) : momentQ (Real.pi / 2 - t) = -momentP t := by
  rw [momentQ, momentP, referenceGD_complement, referenceF_complement]; ring

theorem one_lt_two_mul_A_mul_cosBeta : 1 < 2 * A * cosBeta := by
  rw [mul_assoc, A_mul_cosBeta, mul_one_div, lt_div_iff₀ (by linarith [Y_pos])]
  linarith [Y_lt_three_tenths]

theorem momentP_beta : momentP beta = 0 := by
  rw [momentP_phases, ite_eq_left le_rfl]
  change 1 / 2 - 2 * A * sinBeta = 0
  linarith [four_mul_A_mul_sinBeta]

theorem momentQ_lateSwitch : momentQ lateSwitch = 0 := by
  rw [lateSwitch, momentQ_complement, momentP_beta, neg_zero]

theorem momentP_nonneg_early {t : ℝ} (ht : t ∈ Icc (0 : ℝ) beta) : 0 ≤ momentP t := by
  rw [momentP_phases, ite_eq_left ht.2]
  have hsin : Real.sin t ≤ sinBeta := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [ht.1, Real.pi_pos]) beta_lt_pi_div_two.le ht.2
  nlinarith [four_mul_A_mul_sinBeta, A_pos]

theorem momentP_nonpos_after_beta {t : ℝ} (ht : t ∈ Icc beta (Real.pi / 2)) : momentP t ≤ 0 := by
  rcases ht.1.eq_or_lt with rfl | hbeta
  · exact momentP_beta.le
  rw [momentP_phases, ite_eq_right (not_le.2 hbeta)]
  split_ifs with hmiddle
  · have hsin : Real.sin (beta / 2 + Real.pi / 8) ≤ Real.sin (t / 2 + Real.pi / 8) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [beta_pos, Real.pi_pos])
        (by linarith [ht.2, Real.pi_pos]) (by linarith)
    nlinarith [R_mul_sin_firstPhase, R_pos]
  · have hsin : cosBeta ≤ Real.sin t := by
      simpa only [lateSwitch, Real.sin_pi_div_two_sub, cosBeta] using
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [lateSwitch_pos, Real.pi_pos]) ht.2
          (not_le.1 hmiddle).le
    nlinarith [one_lt_two_mul_A_mul_cosBeta, A_pos]

theorem momentQ_nonneg_before_lateSwitch {t : ℝ} (ht : t ∈ Icc (0 : ℝ) lateSwitch) :
    0 ≤ momentQ t := by
  rw [← sub_sub_cancel (Real.pi / 2) t, momentQ_complement, neg_nonneg]
  exact momentP_nonpos_after_beta ⟨by unfold lateSwitch at ht; linarith [ht.2], by linarith [ht.1]⟩

theorem momentQ_nonpos_late {t : ℝ} (ht : t ∈ Icc lateSwitch (Real.pi / 2)) : momentQ t ≤ 0 := by
  rw [← sub_sub_cancel (Real.pi / 2) t, momentQ_complement, neg_nonpos]
  exact momentP_nonneg_early ⟨by linarith [ht.2], by unfold lateSwitch at ht; linarith [ht.1]⟩

end AmbidextrousSofa.Reference

end BPn12

end BP12

section BP13

noncomputable section BPn13

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

end AmbidextrousSofa.Analysis

end BPn13

end BP13

section BP14

noncomputable section BPn14

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

structure QuarterPair where
  f : ℝ → ℝ
  g : ℝ → ℝ
  fD : ℝ → ℝ
  gD : ℝ → ℝ
  continuous_f : ContinuousOn f (Icc 0 (Real.pi / 2))
  continuous_g : ContinuousOn g (Icc 0 (Real.pi / 2))
  continuous_fD : ContinuousOn fD (Icc 0 (Real.pi / 2))
  continuous_gD : ContinuousOn gD (Icc 0 (Real.pi / 2))
  hasDeriv_f : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt f (fD t) (Ioi t) t
  hasDeriv_g : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt g (gD t) (Ioi t) t

def QuarterPair.sub (p q : QuarterPair) : QuarterPair where
  f := fun t => p.f t - q.f t
  g := fun t => p.g t - q.g t
  fD := fun t => p.fD t - q.fD t
  gD := fun t => p.gD t - q.gD t
  continuous_f := p.continuous_f.sub q.continuous_f
  continuous_g := p.continuous_g.sub q.continuous_g
  continuous_fD := p.continuous_fD.sub q.continuous_fD
  continuous_gD := p.continuous_gD.sub q.continuous_gD
  hasDeriv_f := fun t ht => (p.hasDeriv_f t ht).sub (q.hasDeriv_f t ht)
  hasDeriv_g := fun t ht => (p.hasDeriv_g t ht).sub (q.hasDeriv_g t ht)

end AmbidextrousSofa.Analysis

end BPn14

end BP14

section BP15

noncomputable section BPn15

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

end AmbidextrousSofa.Analysis

end BPn15

end BP15

section BP16

noncomputable section BPn16

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

def QuarterPair.p (u : QuarterPair) (t : ℝ) : ℝ := u.fD t - u.g t + 1

def QuarterPair.q (u : QuarterPair) (t : ℝ) : ℝ := u.gD t + u.f t - 1

def adaptiveDensity (u : QuarterPair) (t : ℝ) : ℝ :=
  (u.f t ^ 2 + u.g t ^ 2 - u.fD t ^ 2 - u.gD t ^ 2 +
    (u.f t - 1) ^ 2 + (u.g t - 1) ^ 2 +
    (u.f t - 1) * u.gD t - (u.g t - 1) * u.fD t -
    min (u.p t) 0 ^ 2 - max (u.q t) 0 ^ 2) / 2

def adaptiveFunctional (u : QuarterPair) : ℝ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), adaptiveDensity u t

def adaptiveLinearDensity (u v : QuarterPair) (t : ℝ) : ℝ :=
  (2 * u.f t - 1) * v.f t + (2 * u.g t - 1) * v.g t -
    u.fD t * v.fD t - u.gD t * v.gD t +
    (v.f t * u.gD t + (u.f t - 1) * v.gD t -
      v.g t * u.fD t - (u.g t - 1) * v.fD t) / 2 -
    min (u.p t) 0 * (v.fD t - v.g t) -
    max (u.q t) 0 * (v.gD t + v.f t)

def adaptiveFirstVariation (u v : QuarterPair) : ℝ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), adaptiveLinearDensity u v t

theorem continuousOn_adaptiveDensity (u : QuarterPair) :
    ContinuousOn (adaptiveDensity u) (Icc 0 (Real.pi / 2)) := by
  unfold adaptiveDensity QuarterPair.p QuarterPair.q; simp only [sq]; (have _a00 := u.continuous_f; have _a01 := u.continuous_g; have _a02 := u.continuous_fD; have _a03 := u.continuous_gD; fun_prop)

theorem continuousOn_adaptiveLinearDensity (u v : QuarterPair) :
    ContinuousOn (adaptiveLinearDensity u v) (Icc 0 (Real.pi / 2)) := by
  unfold adaptiveLinearDensity QuarterPair.p QuarterPair.q; (have _a00 := u.continuous_f; have _a01 := u.continuous_g; have _a02 := u.continuous_fD; have _a03 := u.continuous_gD; have _a10 := v.continuous_f; have _a11 := v.continuous_g; have _a12 := v.continuous_fD; have _a13 := v.continuous_gD; fun_prop)

end AmbidextrousSofa.Analysis

end BPn16

end BP16

section BP17

noncomputable section BPn17

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

def QuarterPair.fluxF (u : QuarterPair) (t : ℝ) : ℝ :=
  -u.fD t - (u.g t - 1) / 2 - min (u.p t) 0

def QuarterPair.fluxG (u : QuarterPair) (t : ℝ) : ℝ :=
  -u.gD t + (u.f t - 1) / 2 - max (u.q t) 0

def QuarterPair.forceF (u : QuarterPair) (t : ℝ) : ℝ :=
  2 * u.f t - 1 + u.gD t / 2 - max (u.q t) 0

def QuarterPair.forceG (u : QuarterPair) (t : ℝ) : ℝ :=
  2 * u.g t - 1 - u.fD t / 2 + min (u.p t) 0

theorem adaptiveFirstVariation_eq_boundary (u v : QuarterPair)
    (hf : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxF (u.forceF t) (Ioi t) t)
    (hg : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxG (u.forceG t) (Ioi t) t) :
    adaptiveFirstVariation u v =
      (u.fluxF (Real.pi / 2) * v.f (Real.pi / 2) +
        u.fluxG (Real.pi / 2) * v.g (Real.pi / 2)) -
      (u.fluxF 0 * v.f 0 + u.fluxG 0 * v.g 0) := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL
    (by unfold QuarterPair.fluxF QuarterPair.fluxG QuarterPair.p QuarterPair.q; (have _a00 := u.continuous_f; have _a01 := u.continuous_g; have _a02 := u.continuous_fD; have _a03 := u.continuous_gD; have _a10 := v.continuous_f; have _a11 := v.continuous_g; have _a12 := v.continuous_fD; have _a13 := v.continuous_gD; refine ContinuousOn.add (ContinuousOn.mul ?_ v.continuous_f) (ContinuousOn.mul ?_ v.continuous_g) <;> fun_prop))
    (fun t ht => (((hf t ht).mul (v.hasDeriv_f t ht)).add
      ((hg t ht).mul (v.hasDeriv_g t ht))).congr_deriv ?_)
    ((continuousOn_adaptiveLinearDensity u v).intervalIntegrable_of_Icc hL)
  unfold adaptiveLinearDensity QuarterPair.forceF QuarterPair.forceG QuarterPair.fluxF
    QuarterPair.fluxG
  ring

end AmbidextrousSofa.Analysis

end BPn17

end BP17

section BP18

noncomputable section BPn18

open Set
open AmbidextrousSofa.Analysis

namespace AmbidextrousSofa.Reference

def referencePair : QuarterPair where
  f := referenceF
  g := referenceG
  fD := referenceFD
  gD := referenceGD
  continuous_f := continuous_referenceF.continuousOn
  continuous_g := continuous_referenceG.continuousOn
  continuous_fD := continuous_referenceFD.continuousOn
  continuous_gD := continuous_referenceGD.continuousOn
  hasDeriv_f := fun t _ => (hasDerivAt_referenceF t).hasDerivWithinAt
  hasDeriv_g := fun t _ => (hasDerivAt_referenceG t).hasDerivWithinAt

theorem min_momentP {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    min (momentP t) 0 = (if t < beta then 0 else momentP t) ∧
      HasDerivWithinAt (fun s => min (momentP s) 0)
        (if t < beta then 0 else referenceFSecond t - referenceGD t) (Ioi t) t := by
  split_ifs with h
  · have h₀ := min_eq_right (momentP_nonneg_early ⟨ht.1.le, h.le⟩)
    refine ⟨h₀, (hasDerivWithinAt_const t _ 0).congr_of_eventuallyEq ?_ h₀⟩
    filter_upwards [Ioo_mem_nhdsGT h] with s hs
    exact min_eq_right (momentP_nonneg_early ⟨ht.1.le.trans hs.1.le, hs.2.le⟩)
  · have h₀ := min_eq_left (momentP_nonpos_after_beta ⟨not_lt.1 h, ht.2.le⟩)
    refine ⟨h₀, (((hasDerivWithinAt_referenceFD_right t).sub
      (hasDerivAt_referenceG t).hasDerivWithinAt).add_const 1).congr_of_eventuallyEq ?_ h₀⟩
    filter_upwards [Ioo_mem_nhdsGT ht.2] with s hs
    exact min_eq_left (momentP_nonpos_after_beta ⟨(not_lt.1 h).trans hs.1.le, hs.2.le⟩)

theorem max_momentQ {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    max (momentQ t) 0 = (if t < lateSwitch then momentQ t else 0) ∧
      HasDerivWithinAt (fun s => max (momentQ s) 0)
        (if t < lateSwitch then referenceGSecond t + referenceFD t else 0) (Ioi t) t := by
  split_ifs with h
  · have h₀ := max_eq_left (momentQ_nonneg_before_lateSwitch ⟨ht.1.le, h.le⟩)
    refine ⟨h₀, (((hasDerivWithinAt_referenceGD_right t).add
      (hasDerivAt_referenceF t).hasDerivWithinAt).sub_const 1).congr_of_eventuallyEq ?_ h₀⟩
    filter_upwards [Ioo_mem_nhdsGT h] with s hs
    exact max_eq_left (momentQ_nonneg_before_lateSwitch ⟨ht.1.le.trans hs.1.le, hs.2.le⟩)
  · have h₀ := max_eq_right (momentQ_nonpos_late ⟨not_lt.1 h, ht.2.le⟩)
    refine ⟨h₀, (hasDerivWithinAt_const t _ 0).congr_of_eventuallyEq ?_ h₀⟩
    filter_upwards [Ioo_mem_nhdsGT ht.2] with s hs
    exact max_eq_right (momentQ_nonpos_late ⟨(not_lt.1 h).trans hs.1.le, hs.2.le⟩)

theorem referencePair_eulerF {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt referencePair.fluxF (referencePair.forceF t) (Ioi t) t := by
  refine (((hasDerivWithinAt_referenceFD_right t).neg.sub
    (((hasDerivAt_referenceG t).hasDerivWithinAt.sub_const 1).div_const 2)).sub
    (min_momentP ht).2).congr_deriv ?_
  rw [QuarterPair.forceF, show max (referencePair.q t) 0 = _ from (max_momentQ ht).1]
  simp only [momentQ, referencePair, referenceF_eq_right_phases, referenceFSecond,
    referenceGD, phases_eq_right gD_matching_first gD_matching_last]
  split_ifs <;> first
    | (exfalso; linarith [beta_lt_lateSwitch])
    | (simp only [fEarly, fMiddle, fLate, gEarlyD, gMiddleD, gLateD]; ring)

theorem referencePair_eulerG {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt referencePair.fluxG (referencePair.forceG t) (Ioi t) t := by
  refine (((hasDerivWithinAt_referenceGD_right t).neg.add
    (((hasDerivAt_referenceF t).hasDerivWithinAt.sub_const 1).div_const 2)).sub
    (max_momentQ ht).2).congr_deriv ?_
  rw [QuarterPair.forceG, show min (referencePair.p t) 0 = _ from (min_momentP ht).1]
  simp only [momentP, referencePair, referenceG_eq_right_phases, referenceGSecond,
    referenceFD, phases_eq_right fD_matching_first fD_matching_last]
  split_ifs <;> first
    | (exfalso; linarith [beta_lt_lateSwitch])
    | (simp only [gEarly, gMiddle, gLate, fEarlyD, fMiddleD, fLateD]; ring)

end AmbidextrousSofa.Reference

end BPn18

end BP18

section BP19

noncomputable section BPn19

namespace AmbidextrousSofa

def companionNormal (θ : ℝ) : Plane := (-Real.sin θ, Real.cos θ)

theorem continuous_companionNormal : Continuous companionNormal := by
  unfold companionNormal; fun_prop

theorem companionNormal_eq_unitNormal (θ : ℝ) :
    companionNormal θ = unitNormal (θ + Real.pi / 2) := by
  apply Prod.ext <;> simp [companionNormal, unitNormal, Real.sin_add, Real.cos_add]

def frameHall (u v : Plane) (a b : ℝ) : Set Plane :=
  {p | coordDot p u ≤ a + 1 ∧ coordDot p v ≤ b + 1 ∧
    (a ≤ coordDot p u ∨ b ≤ coordDot p v)}

def canonicalHall (K : Set Plane) (u v : Plane) : Set Plane :=
  frameHall u v (support K u - 1) (support K v - 1)

theorem mem_canonicalHall (K : Set Plane) (u v p : Plane) :
    p ∈ canonicalHall K u v ↔
      coordDot p u ≤ support K u ∧ coordDot p v ≤ support K v ∧
        (support K u - 1 ≤ coordDot p u ∨ support K v - 1 ≤ coordDot p v) := by
  simp only [canonicalHall, frameHall, Set.mem_ofPred_eq, sub_add_cancel]

def canonicalPlacement (K : Set Plane) (θ : ℝ) (p : Plane) : Plane :=
  (coordDot p (unitNormal θ) + 1 - support K (unitNormal θ),
    coordDot p (companionNormal θ) + 1 - support K (companionNormal θ))

theorem canonicalPlacement_eq_rigidMap (K : Set Plane) (θ : ℝ) (p : Plane) :
    canonicalPlacement K θ p =
      rigidMap (-θ) (1 - support K (unitNormal θ),
        1 - support K (companionNormal θ)) p := by
  apply Prod.ext <;>
    simp only [canonicalPlacement, rigidMap, rotate, coordDot, unitNormal,
      companionNormal, Prod.fst_add, Prod.snd_add, Real.cos_neg, Real.sin_neg] <;> ring

theorem rigidMap_mem_lowerHall_iff (θ : ℝ) (a p : Plane) :
    rigidMap (-θ) a p ∈ lowerHall ↔
      p ∈ frameHall (unitNormal θ) (companionNormal θ) (-a.1) (-a.2) := by
  simp only [lowerHall, incomingArm, lowerOutgoingArm, frameHall, Set.mem_union,
    Set.mem_ofPred_eq, rigidMap, rotate, coordDot, unitNormal, companionNormal, Prod.fst_add,
    Prod.snd_add, Real.cos_neg, Real.sin_neg]
  grind

theorem canonicalPlacement_mem_lowerHall_iff (K : Set Plane) (θ : ℝ) (p : Plane) :
    canonicalPlacement K θ p ∈ lowerHall ↔
      p ∈ canonicalHall K (unitNormal θ) (companionNormal θ) := by
  rw [canonicalPlacement_eq_rigidMap, rigidMap_mem_lowerHall_iff, canonicalHall, neg_sub, neg_sub]

end AmbidextrousSofa

end BPn19

end BP19

section BP20

noncomputable section BPn20

namespace AmbidextrousSofa

def firstWall (K : Set Plane) (θ x : ℝ) : ℝ :=
  (support K (unitNormal θ) - 1 - x * Real.cos θ) / Real.sin θ

def secondWall (K : Set Plane) (θ x : ℝ) : ℝ :=
  (support K (companionNormal θ) - 1 + x * Real.sin θ) / Real.cos θ

def cornerWall (K : Set Plane) (θ x : ℝ) : ℝ := min (firstWall K θ x) (secondWall K θ x)

def sweptWallValues (K : Set Plane) (α x : ℝ) : Set ℝ :=
  (fun θ => cornerWall K θ x) '' Set.Ioo 0 α

def sweptNiche (K : Set Plane) (α x : ℝ) : ℝ := max (sSup (sweptWallValues K α x)) 0

theorem sweptWallValues_nonempty (K : Set Plane) {α : ℝ} (hα : 0 < α) (x : ℝ) :
    (sweptWallValues K α x).Nonempty :=
  (Set.nonempty_Ioo.2 hα).image _

theorem sweptNiche_nonneg (K : Set Plane) (α x : ℝ) : 0 ≤ sweptNiche K α x := le_max_right _ _

theorem firstWall_le_iff {K : Set Plane} {θ x y : ℝ} (hs : 0 < Real.sin θ) :
    firstWall K θ x ≤ y ↔ support K (unitNormal θ) - 1 ≤ coordDot (x, y) (unitNormal θ) := by
  rw [firstWall, div_le_iff₀ hs, sub_le_iff_le_add']; rfl

theorem secondWall_le_iff {K : Set Plane} {θ x y : ℝ} (hc : 0 < Real.cos θ) :
    secondWall K θ x ≤ y ↔
      support K (companionNormal θ) - 1 ≤ coordDot (x, y) (companionNormal θ) := by
  rw [secondWall, div_le_iff₀ hc]
  simp only [coordDot, companionNormal]
  constructor <;> intro h <;> linarith

theorem cornerWall_le_iff {K : Set Plane} {θ x y : ℝ}
    (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) :
    cornerWall K θ x ≤ y ↔
      (support K (unitNormal θ) - 1 ≤ coordDot (x, y) (unitNormal θ) ∨
        support K (companionNormal θ) - 1 ≤ coordDot (x, y) (companionNormal θ)) := by
  rw [cornerWall, min_le_iff, firstWall_le_iff hs, secondWall_le_iff hc]

theorem sweptNiche_le_of_forall {K : Set Plane} {α x y : ℝ} (hα : 0 < α)
    (hy : 0 ≤ y) (h : ∀ θ ∈ Set.Ioo 0 α, cornerWall K θ x ≤ y) :
    sweptNiche K α x ≤ y :=
  max_le (csSup_le (sweptWallValues_nonempty K hα x) (Set.forall_mem_image.mpr h)) hy

theorem cornerWall_le_sweptNiche {K : Set Plane} {α θ x : ℝ}
    (hbounded : BddAbove (sweptWallValues K α x)) (hθ : θ ∈ Set.Ioo 0 α) :
    cornerWall K θ x ≤ sweptNiche K α x :=
  (le_csSup hbounded (Set.mem_image_of_mem _ hθ)).trans (le_max_left _ _)

end AmbidextrousSofa

end BPn20

end BP20

section BP21

noncomputable section BPn21

open Set MeasureTheory

namespace AmbidextrousSofa

theorem exists_support_upper_bound_quarterTurn {K : Set Plane} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Icc (0 : ℝ) (Real.pi / 2),
      support K (unitNormal θ) ≤ C ∧ support K (companionNormal θ) ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).bddAbove_image
    (((continuous_support hK).comp continuous_unitNormal).max
      ((continuous_support hK).comp continuous_companionNormal)).continuousOn
  exact ⟨max C 0, le_max_right _ _, fun θ hθ =>
    max_le_iff.1 ((hC (mem_image_of_mem _ hθ)).trans (le_max_left _ _))⟩

theorem half_le_sin_or_half_le_cos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    (1 / 2 : ℝ) ≤ Real.sin θ ∨ (1 / 2 : ℝ) ≤ Real.cos θ := by
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter hθ
  by_contra! h
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem cornerWall_le_of_support_bounds {K : Set Plane} {θ C : ℝ}
    (hC : 0 ≤ C) (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hu : support K (unitNormal θ) ≤ C)
    (hv : support K (companionNormal θ) ≤ C) (x : ℝ) :
    cornerWall K θ x ≤ 2 * (C + 1 + |x|) := by
  have hN : 0 ≤ C + 1 + |x| := by positivity
  have hx : ∀ t, |t| ≤ 1 → -|x| ≤ x * t ∧ x * t ≤ |x| := fun t ht =>
    abs_le.1 ((abs_mul x t).trans_le (mul_le_of_le_one_right (abs_nonneg x) ht))
  rcases half_le_sin_or_half_le_cos hθ with hs | hc
  · refine (min_le_left _ _).trans ?_
    rw [firstWall, div_le_iff₀ (by linarith)]
    linarith [(hx _ (Real.abs_cos_le_one θ)).1, mul_nonneg hN (sub_nonneg.mpr hs)]
  · refine (min_le_right _ _).trans ?_
    rw [secondWall, div_le_iff₀ (by linarith)]
    linarith [(hx _ (Real.abs_sin_le_one θ)).2, mul_nonneg hN (sub_nonneg.mpr hc)]

theorem sweptWallValues_bddAbove {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα : α ≤ Real.pi / 2) (x : ℝ) :
    BddAbove (sweptWallValues K α x) := by
  obtain ⟨C, hC, hS⟩ := exists_support_upper_bound_quarterTurn hK
  refine ⟨2 * (C + 1 + |x|), forall_mem_image.2 fun θ hθ => ?_⟩
  have hθ' : θ ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ.1, hθ.2.trans_le hα⟩
  obtain ⟨hu, hv⟩ := hS θ (Ioo_subset_Icc_self hθ')
  exact cornerWall_le_of_support_bounds hC hθ' hu hv x

theorem integrableOn_capRoof_Icc {K : Set Plane} (hK : IsCompact K)
    (hStrip : K ⊆ unitStrip) (l r : ℝ) :
    IntegrableOn (capRoof K) (Icc l r) := by
  have hK0 : ∀ p ∈ K, 0 ≤ p.2 := fun p hp => (hStrip hp).1
  refine .of_bound measure_Icc_lt_top (measurable_capRoof hK hK0).aestronglyMeasurable 1
    (.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (capRoof_nonneg hK hK0 x)]
  exact capRoof_le_one hK hStrip x

theorem integrableOn_roofDeficit_Icc {K : Set Plane} (hK : IsCompact K)
    (hStrip : K ⊆ unitStrip) (l r : ℝ) :
    IntegrableOn (fun x => 1 - capRoof K x) (Icc l r) :=
  (integrableOn_const measure_Icc_lt_top.ne).sub (integrableOn_capRoof_Icc hK hStrip l r)

theorem IsDownwardCap.integrableOn_capRoof_Icc {U : Set Plane}
    (hU : IsDownwardCap U) (l r : ℝ) : IntegrableOn (capRoof U) (Icc l r) :=
  AmbidextrousSofa.integrableOn_capRoof_Icc hU.isCompact hU.inStrip l r

theorem IsDownwardCap.integrableOn_roofDeficit_Icc {U : Set Plane}
    (hU : IsDownwardCap U) (l r : ℝ) :
    IntegrableOn (fun x => 1 - capRoof U x) (Icc l r) :=
  AmbidextrousSofa.integrableOn_roofDeficit_Icc hU.isCompact hU.inStrip l r

end AmbidextrousSofa

end BPn21

end BP21

section BP22

noncomputable section BPn22

open Set
open scoped Topology

namespace AmbidextrousSofa.Reference

def referenceNiche (x : ℝ) : ℝ := sweptNiche referenceHull (Real.pi / 2) x

def referenceApexHeight (t : ℝ) : ℝ :=
  (referenceF t - 1) * Real.sin t + (referenceG t - 1) * Real.cos t

def referenceWallClip (x t : ℝ) : ℝ :=
  max (min ((referenceF t - 1 - x * Real.cos t) / Real.sin t)
    ((referenceG t - 1 + x * Real.sin t) / Real.cos t)) 0

theorem R_lt_sqrt_two : R < Real.sqrt 2 := by
  obtain ⟨h₁, h₂, -⟩ := middlePhase_bounds le_rfl beta_lt_lateSwitch.le
  refine Real.lt_sqrt_of_sq_lt ?_
  have hR : R ^ 2 = (R * Real.cos (beta / 2 + Real.pi / 8)) ^ 2 +
      (R * Real.sin (beta / 2 + Real.pi / 8)) ^ 2 := by
    linear_combination -R ^ 2 * Real.cos_sq_add_sin_sq (beta / 2 + Real.pi / 8)
  rw [hR, R_mul_sin_firstPhase]
  nlinarith

theorem continuous_referenceApexHeight : Continuous referenceApexHeight :=
  ((continuous_referenceF.sub continuous_const).mul Real.continuous_sin).add
    ((continuous_referenceG.sub continuous_const).mul Real.continuous_cos)

theorem referenceApexHeight_zero : referenceApexHeight 0 = 0 := by
  simp [referenceApexHeight, referenceF_zero, referenceG_zero]

theorem earlyApex_lt_half {t : ℝ} (ht : t ∈ Icc (0 : ℝ) beta) :
    (fEarly t - 1) * Real.sin t + (gEarly t - 1) * Real.cos t < 1 / 2 := by
  have hs : Real.sin t ≤ sinBeta := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [ht.1, Real.pi_pos]) beta_lt_pi_div_two.le ht.2
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], ht.2.trans_lt beta_lt_pi_div_two⟩
  have hA : 4 * A * Real.sin t ≤ 1 := by
    linarith [mul_le_mul_of_nonneg_left hs A_pos.le, four_mul_A_mul_sinBeta]
  rcases ht.1.eq_or_lt with rfl | ht0
  · norm_num [fEarly, gEarly]
  · have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0
      (by linarith [ht.2, beta_lt_pi_div_two, Real.pi_pos])
    unfold fEarly gEarly
    linarith [mul_le_mul_of_nonneg_right hA hc.le, Real.sin_sq_add_cos_sq t]

theorem middlePhase_sin_le_cos_center {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    Real.sin (3 / 2 * t + Real.pi / 8) ≤ Real.cos (t - Real.pi / 4) := by
  have hu : |t - Real.pi / 4| ≤ Real.pi / 4 :=
    abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [show 3 / 2 * t + Real.pi / 8 = 3 / 2 * (t - Real.pi / 4) + Real.pi / 2 by ring,
    Real.sin_add_pi_div_two, ← Real.cos_abs (3 / 2 * _), ← Real.cos_abs (t - _), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
    (by linarith [abs_nonneg (t - Real.pi / 4)])

theorem middleApex_lt_half {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (fMiddle t - 1) * Real.sin t + (gMiddle t - 1) * Real.cos t < 1 / 2 := by
  have hcos : 0 < Real.cos (t - Real.pi / 4) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  have hsum : Real.sin t + Real.cos t = Real.sqrt 2 * Real.cos (t - Real.pi / 4) := by
    rw [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
    linear_combination (-(Real.cos t + Real.sin t) / 2) * Real.sq_sqrt (zero_le_two (α := ℝ))
  have hsin : R * Real.sin (3 / 2 * t + Real.pi / 8) =
      R * Real.sin (t / 2 + Real.pi / 8) * Real.cos t +
        R * Real.cos (t / 2 + Real.pi / 8) * Real.sin t := by
    rw [show 3 / 2 * t + Real.pi / 8 = (t / 2 + Real.pi / 8) + t by ring, Real.sin_add]; ring
  unfold fMiddle gMiddle
  linarith [mul_le_mul_of_nonneg_left (middlePhase_sin_le_cos_center ht) R_pos.le,
    mul_lt_mul_of_pos_right R_lt_sqrt_two hcos, Real.sin_sq_add_cos_sq t]

theorem referenceApexHeight_lt_half {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceApexHeight t < 1 / 2 := by

  wlog hlate : t ≤ lateSwitch generalizing t
  · have h := this (t := Real.pi / 2 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      (by unfold lateSwitch at hlate ⊢; linarith [beta_lt_pi_div_four])
    simp only [referenceApexHeight, referenceF_complement, referenceG_complement,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at h ⊢
    linarith
  unfold referenceApexHeight referenceF referenceG
  split_ifs with hearly
  · exact earlyApex_lt_half ⟨ht.1, hearly⟩
  · exact middleApex_lt_half ht

theorem firstWall_referenceHull {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    firstWall referenceHull t x =
      (referenceF t - 1 - x * Real.cos t) / Real.sin t := by
  rw [firstWall, ← angleSupport, angleSupport_referenceHull_eq_f ht]

theorem secondWall_referenceHull {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    secondWall referenceHull t x =
      (referenceG t - 1 + x * Real.sin t) / Real.cos t := by
  rw [secondWall, companionNormal_eq_unitNormal, ← angleSupport,
    angleSupport_referenceHull_eq_g ht]

theorem referenceNiche_mirror (x : ℝ) : referenceNiche (2 * k - x) = referenceNiche x := by
  have h : EqOn (fun t => cornerWall referenceHull t (2 * k - x))
      ((fun t => cornerWall referenceHull t x) ∘ (Real.pi / 2 - ·)) (Ioo 0 (Real.pi / 2)) := by
    intro t ht
    have hs : Real.pi / 2 - t ∈ Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [Function.comp_apply, cornerWall, firstWall_referenceHull (Ioo_subset_Icc_self ht),
      secondWall_referenceHull (Ioo_subset_Icc_self ht), firstWall_referenceHull hs,
      secondWall_referenceHull hs, referenceF_complement, referenceG_complement,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    rw [min_comm]
    congr 1 <;> ring
  unfold referenceNiche sweptNiche sweptWallValues
  rw [h.image_eq, image_comp, image_const_sub_Ioo, sub_self, sub_zero]

theorem cornerWall_referenceHull_le_apex {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    cornerWall referenceHull t x ≤ referenceApexHeight t := by
  have hs : Real.sin t ≠ 0 := (sin_cos_pos_of_mem_quarter ht).1.ne'
  have hc : Real.cos t ≠ 0 := (sin_cos_pos_of_mem_quarter ht).2.ne'
  calc cornerWall referenceHull t x = cornerWall referenceHull t x * Real.sin t ^ 2 +
        cornerWall referenceHull t x * Real.cos t ^ 2 := by
        rw [← mul_add, Real.sin_sq_add_cos_sq, mul_one]
    _ ≤ firstWall referenceHull t x * Real.sin t ^ 2 +
        secondWall referenceHull t x * Real.cos t ^ 2 := by
        gcongr
        exacts [min_le_left _ _, min_le_right _ _]
    _ = referenceApexHeight t := by
        rw [firstWall_referenceHull ⟨ht.1.le, ht.2.le⟩,
          secondWall_referenceHull ⟨ht.1.le, ht.2.le⟩, referenceApexHeight]
        field_simp
        ring

theorem referenceNiche_nonneg (x : ℝ) : 0 ≤ referenceNiche x :=
  sweptNiche_nonneg referenceHull (Real.pi / 2) x

theorem referenceNiche_lt_half (x : ℝ) : referenceNiche x < 1 / 2 := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, hzero⟩
    continuous_referenceApexHeight.continuousOn
  refine (sweptNiche_le_of_forall (by linarith [Real.pi_pos])
    (referenceApexHeight_zero.symm.trans_le (hmax hzero)) fun s hs => ?_).trans_lt
    (referenceApexHeight_lt_half ht)
  exact (cornerWall_referenceHull_le_apex hs x).trans (hmax ⟨hs.1.le, hs.2.le⟩)

theorem referenceWallClip_zero (x : ℝ) : referenceWallClip x 0 = 0 := by
  simp [referenceWallClip, referenceF_zero, referenceG_zero]

theorem referenceWallClip_pi_div_two (x : ℝ) : referenceWallClip x (Real.pi / 2) = 0 := by
  simp [referenceWallClip, referenceF_pi_div_two]

theorem referenceWallClip_eq_actual {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    referenceWallClip x t = max (cornerWall referenceHull t x) 0 := by
  rw [cornerWall, firstWall_referenceHull ht, secondWall_referenceHull ht]
  rfl

private theorem continuousAt_of_nonneg_of_le {f u : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hu : ContinuousAt u z) (hu0 : u z = 0) (hf0 : f z = 0) (hf : ∀ p, 0 ≤ f p)
    (hfu : ∀ p, f p ≤ u p) :
    ContinuousAt f z := by
  rw [ContinuousAt, hf0]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu0 ▸ hu.tendsto) hf hfu

theorem continuousAt_referenceWallClip {z : ℝ × ℝ}
    (hz : z.2 ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ContinuousAt (fun p : ℝ × ℝ => referenceWallClip p.1 p.2) z := by
  have hf := continuous_referenceF
  have hg := continuous_referenceG
  have hclip (p : ℝ × ℝ) : 0 ≤ referenceWallClip p.1 p.2 := le_max_right _ _
  by_cases hz0 : z.2 = 0
  · exact continuousAt_of_nonneg_of_le
      (u := fun p => max ((referenceG p.2 - 1 + p.1 * Real.sin p.2) / Real.cos p.2) 0)
      (by fun_prop (disch := simp [hz0])) (by simp [hz0, referenceG_zero])
      (by simp [hz0, referenceWallClip_zero]) hclip
      fun p => max_le_max_right 0 (min_le_right _ _)
  by_cases hzL : z.2 = Real.pi / 2
  · exact continuousAt_of_nonneg_of_le
      (u := fun p => max ((referenceF p.2 - 1 - p.1 * Real.cos p.2) / Real.sin p.2) 0)
      (by fun_prop (disch := simp [hzL])) (by simp [hzL, referenceF_pi_div_two])
      (by simp [hzL, referenceWallClip_pi_div_two]) hclip
      fun p => max_le_max_right 0 (min_le_left _ _)
  have hsin : Real.sin z.2 ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi
    (lt_of_le_of_ne hz.1 (Ne.symm hz0)) (by linarith [hz.2, Real.pi_pos])).ne'
  have hcos : Real.cos z.2 ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hz.1, Real.pi_pos], lt_of_le_of_ne hz.2 hzL⟩).ne'
  unfold referenceWallClip
  fun_prop (disch := assumption)

theorem continuous_referenceWallClip_on_angles :
    Continuous (fun p : ℝ × Icc (0 : ℝ) (Real.pi / 2) => referenceWallClip p.1 p.2) :=
  continuous_iff_continuousAt.2 fun p =>
    (continuousAt_referenceWallClip (z := (p.1, (p.2 : ℝ))) p.2.2).comp
      (f := fun q : ℝ × Icc (0 : ℝ) (Real.pi / 2) => (q.1, (q.2 : ℝ))) (by fun_prop)

theorem referenceNiche_eq_sSup_clipped (x : ℝ) :
    referenceNiche x = sSup ((fun t : Icc (0 : ℝ) (Real.pi / 2) =>
      referenceWallClip x t) '' Set.univ) := by
  let zeroAngle : Icc (0 : ℝ) (Real.pi / 2) := ⟨0, le_rfl, by linarith [Real.pi_pos]⟩
  have hbounded := isCompact_univ.bddAbove_image (continuous_referenceWallClip_on_angles.comp
    (continuous_const.prodMk continuous_id) (f := fun t => (x, t))).continuousOn
  have hzero := le_csSup_of_le hbounded (mem_image_of_mem _ (mem_univ zeroAngle))
    (referenceWallClip_zero x).ge
  apply le_antisymm
  · exact sweptNiche_le_of_forall (by linarith [Real.pi_pos]) hzero fun t ht =>
      le_csSup_of_le hbounded (mem_image_of_mem _ (mem_univ ⟨t, ht.1.le, ht.2.le⟩))
        ((le_max_left _ _).trans (referenceWallClip_eq_actual ⟨ht.1.le, ht.2.le⟩ x).ge)
  · refine csSup_le ⟨_, mem_image_of_mem _ (mem_univ zeroAngle)⟩ ?_
    rintro _ ⟨⟨t, ht⟩, -, rfl⟩
    rcases ht.1.eq_or_lt with rfl | h0
    · exact (referenceWallClip_zero x).trans_le (referenceNiche_nonneg x)
    rcases ht.2.eq_or_lt with rfl | hL
    · exact (referenceWallClip_pi_div_two x).trans_le (referenceNiche_nonneg x)
    exact (referenceWallClip_eq_actual ht x).trans_le (max_le (cornerWall_le_sweptNiche
      (sweptWallValues_bddAbove isCompact_referenceHull le_rfl x) ⟨h0, hL⟩)
      (referenceNiche_nonneg x))

theorem continuous_referenceNiche : Continuous referenceNiche := by
  rw [funext referenceNiche_eq_sSup_clipped]
  exact isCompact_univ.continuous_sSup continuous_referenceWallClip_on_angles

end AmbidextrousSofa.Reference

end BPn22

end BP22

section BP23

namespace AmbidextrousSofa

noncomputable def signedFiberLength (dU dV nU nV : ℝ) : ℝ :=
  1 - max dV nU - max dU nV

def fourWallFiber (dU dV nU nV : ℝ) : Set ℝ :=
  {y | dV ≤ y ∧ nU ≤ y ∧ y ≤ 1 - dU ∧ y ≤ 1 - nV}

theorem fourWallFiber_eq_Icc (dU dV nU nV : ℝ) :
    fourWallFiber dU dV nU nV =
      Set.Icc (max dV nU) (1 - max dU nV) := by
  ext y
  simp only [fourWallFiber, Set.mem_ofPred_eq, Set.mem_Icc, max_le_iff, le_sub_comm (a := y),
    and_assoc]

end AmbidextrousSofa

end BP23

section BP24

open Set MeasureTheory

namespace AmbidextrousSofa

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
variable (μ : Measure X) [μ.IsOpenPosMeasure]

end AmbidextrousSofa

end BP24

section BP25

noncomputable section BPn25

open Set MeasureTheory

namespace AmbidextrousSofa

def verticalIntervalRegion (I : Set ℝ) (lower upper : ℝ → ℝ) : Set Plane :=
  {p | p.1 ∈ I ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}

theorem volume_verticalIntervalRegion_eq_lintegral
    {I : Set ℝ} {lower upper : ℝ → ℝ}
    (hI : MeasurableSet I) (hLower : Measurable lower) (hUpper : Measurable upper) :
    volume (verticalIntervalRegion I lower upper) =
      ∫⁻ x in I, ENNReal.ofReal (upper x - lower x) := by
  have hm : MeasurableSet (verticalIntervalRegion I lower upper) :=
    measurableSet_region_between_cc hLower hUpper hI
  rw [Measure.volume_eq_prod, Measure.prod_apply hm, ← lintegral_indicator hI]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ I <;> simp [verticalIntervalRegion, hx, Icc_def]

def fourWallEnvelope (I : Set ℝ) (dU dV nU nV : ℝ → ℝ) : Set Plane :=
  {p | p.1 ∈ I ∧ p.2 ∈ fourWallFiber (dU p.1) (dV p.1) (nU p.1) (nV p.1)}

theorem integrableOn_signedFiberLength {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hFinite : volume I ≠ ⊤)
    (hdU : IntegrableOn dU I) (hdV : IntegrableOn dV I)
    (hnU : IntegrableOn nU I) (hnV : IntegrableOn nV I) :
    IntegrableOn (fun x => signedFiberLength (dU x) (dV x) (nU x) (nV x)) I :=
  ((integrableOn_const hFinite).sub (Integrable.sup hdV hnU)).sub (Integrable.sup hdU hnV)

theorem volume_fourWallEnvelope_eq_ofReal_signedIntegral
    {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hI : MeasurableSet I) (hdU : Measurable dU) (hdV : Measurable dV)
    (hnU : Measurable nU) (hnV : Measurable nV)
    (hSigned : IntegrableOn (fun x => signedFiberLength (dU x) (dV x) (nU x) (nV x)) I)
    (hNonneg : ∀ᵐ x ∂volume.restrict I, 0 ≤ signedFiberLength (dU x) (dV x) (nU x) (nV x)) :
    volume (fourWallEnvelope I dU dV nU nV) =
      ENNReal.ofReal (∫ x in I, signedFiberLength (dU x) (dV x) (nU x) (nV x)) := by
  have h : fourWallEnvelope I dU dV nU nV = verticalIntervalRegion I
      (fun x => max (dV x) (nU x)) (fun x => 1 - max (dU x) (nV x)) :=
    ext fun p => and_congr_right fun _ => by rw [fourWallFiber_eq_Icc]
  rw [h, volume_verticalIntervalRegion_eq_lintegral (upper := fun x => 1 - max (dU x) (nV x)) hI
    (hdV.max hnU) (measurable_const.sub (hdU.max hnV)),
    ofReal_integral_eq_lintegral_ofReal hSigned hNonneg]
  exact lintegral_congr fun x => by rw [signedFiberLength, sub_right_comm]

theorem volumeReal_fourWallEnvelope_eq_signedIntegral
    {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hI : MeasurableSet I) (hdU : Measurable dU) (hdV : Measurable dV)
    (hnU : Measurable nU) (hnV : Measurable nV)
    (hSigned : IntegrableOn (fun x => signedFiberLength (dU x) (dV x) (nU x) (nV x)) I)
    (hNonneg : ∀ᵐ x ∂volume.restrict I, 0 ≤ signedFiberLength (dU x) (dV x) (nU x) (nV x)) :
    volume.real (fourWallEnvelope I dU dV nU nV) =
      ∫ x in I, signedFiberLength (dU x) (dV x) (nU x) (nV x) := by
  rw [measureReal_def,
    volume_fourWallEnvelope_eq_ofReal_signedIntegral hI hdU hdV hnU hnV hSigned hNonneg,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hNonneg)]

end AmbidextrousSofa

end BPn25

end BP25

section BP26

noncomputable section BPn26

open Set MeasureTheory

namespace AmbidextrousSofa

end AmbidextrousSofa

end BPn26

end BP26

section BP27

noncomputable section BPn27

open Set MeasureTheory

namespace AmbidextrousSofa

def roofDeficit (U : Set Plane) (x : ℝ) : ℝ := 1 - capRoof U x

def capWidth (U : Set Plane) : ℝ := horizontalRight U - horizontalLeft U

theorem IsDownwardCap.measurable_roofDeficit {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (roofDeficit U) :=
  measurable_const.sub hU.measurable_capRoof

end AmbidextrousSofa

end BPn27

end BP27

section BP28

noncomputable section BPn28

open Set

namespace AmbidextrousSofa.Reference

def topLeft : ℝ := 1 - 2 * A

def topRight : ℝ := 1 - 2 / 3 * A

def topInterval : Set ℝ := Icc topLeft topRight

theorem topLeft_lt_topRight : topLeft < topRight := by
  unfold topLeft topRight; linarith [A_pos]

theorem horizontalLeft_referenceCap : horizontalLeft referenceCap = 1 - 8 / 3 * A := by
  have h := angleSupport_referenceHull_eq_g (t := Real.pi / 2) ⟨by positivity, le_rfl⟩
  simp only [add_halves, angleSupport, unitNormal, Real.cos_pi, Real.sin_pi,
    referenceG_pi_div_two, support_horizontal_left isCompact_referenceHull
      referenceHull_nonempty] at h
  unfold horizontalLeft at h ⊢
  rw [horizontalProjection_referenceCap]
  linarith

theorem horizontalRight_referenceCap : horizontalRight referenceCap = 1 := by
  have h := angleSupport_referenceHull_eq_f (t := 0) ⟨le_rfl, by positivity⟩
  simp only [angleSupport, unitNormal, Real.cos_zero, Real.sin_zero, support_horizontal_right,
    referenceF_zero] at h
  rwa [horizontalRight, horizontalProjection_referenceCap]

theorem capWidth_referenceCap : capWidth referenceCap = 8 / 3 * A := by
  rw [capWidth, horizontalLeft_referenceCap, horizontalRight_referenceCap]; ring

theorem topFace_mem_referenceHull {x : ℝ} (hx : x ∈ topInterval) : (x, 1) ∈ referenceHull := by
  have hr : (topRight, (1 : ℝ)) ∈ referenceHull := by
    simpa only [fBoundary_pi_div_two, topRight] using
      fBoundary_mem_referenceHull (t := Real.pi / 2) ⟨by positivity, le_rfl⟩

  have hl : (topLeft, (1 : ℝ)) ∈ referenceHull := by
    convert (mirror_mem_referenceHull _).2 hr using 2; unfold topLeft topRight k; ring
  apply convex_referenceHull.segment_subset hl hr
  rw [← Prod.image_mk_segment_left, segment_eq_Icc topLeft_lt_topRight.le]
  exact mem_image_of_mem _ hx

theorem capRoof_referenceCap_eq_one {x : ℝ} (hx : x ∈ topInterval) :
    capRoof referenceCap x = 1 :=
  le_antisymm (capRoof_le_one isDownwardCap_referenceCap.isCompact
    isDownwardCap_referenceCap.inStrip x) (le_capRoof isDownwardCap_referenceCap.isCompact
      (referenceHull_subset_referenceCap (topFace_mem_referenceHull hx)))

theorem referenceF_le_topRight_disk {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceF t ≤ 1 + topRight * Real.cos t := by
  have hf := continuous_referenceF
  have hfD := continuous_referenceFD
  have h := supportProjection_le_self (h := fun x => 1 + topRight * Real.cos x - referenceF x)
    (hD := fun x => -topRight * Real.sin x - referenceFD x)
    (hDD := fun x => -topRight * Real.cos x - referenceFSecond x) (by fun_prop) (by fun_prop)
    (fun x => (((hasDerivAt_const x 1).add ((Real.hasDerivAt_cos x).const_mul topRight)).sub
      (hasDerivAt_referenceF x)).hasDerivWithinAt.congr_deriv (by ring))
    (fun x => ((Real.hasDerivAt_sin x).const_mul (-topRight)).hasDerivWithinAt.sub
      (hasDerivWithinAt_referenceFD_right x))
    (fun x _ => by linarith [(referenceF_right_curvature x).2])
    (by linarith [Real.pi_pos]) ⟨by positivity, le_rfl⟩ ht
  simpa [supportProjection, referenceF_pi_div_two, referenceFD_pi_div_two, topRight] using h

theorem referenceNiche_eq_zero_of_topRight_le {x : ℝ} (hx : topRight ≤ x) :
    referenceNiche x = 0 := by
  refine le_antisymm (sweptNiche_le_of_forall (by positivity) le_rfl fun t ht => ?_)
    (referenceNiche_nonneg x)
  refine (min_le_left _ _).trans ?_
  rw [firstWall_referenceHull ⟨ht.1.le, ht.2.le⟩]
  refine div_nonpos_of_nonpos_of_nonneg ?_
    (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2, Real.pi_pos]))
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩
  linarith [referenceF_le_topRight_disk ⟨ht.1.le, ht.2.le⟩, mul_le_mul_of_nonneg_right hx hc]

theorem referenceNiche_eq_zero_of_le_topLeft {x : ℝ} (hx : x ≤ topLeft) : referenceNiche x = 0 := by
  rw [← sub_sub_cancel (2 * k) x, referenceNiche_mirror]
  exact referenceNiche_eq_zero_of_topRight_le (by unfold topLeft topRight k at *; linarith)

theorem referenceNiche_eq_zero_outside {x : ℝ} (hx : x ∉ topInterval) : referenceNiche x = 0 := by
  rcases le_total x topLeft with hl | hl
  · exact referenceNiche_eq_zero_of_le_topLeft hl
  · exact referenceNiche_eq_zero_of_topRight_le (not_lt.1 fun hr => hx ⟨hl, hr.le⟩)

end AmbidextrousSofa.Reference

end BPn28

end BP28

section BP29

noncomputable section BPn29

open Set

namespace AmbidextrousSofa

structure AngularConstraints (S K : Set Plane) (α : ℝ) : Prop where
  angle_pos : 0 < α
  angle_le : α ≤ Real.pi / 2
  inside : ∀ θ ∈ Ioo 0 α, S ⊆ canonicalHall K (unitNormal θ) (companionNormal θ)
  terminal : ∀ p ∈ S, support K (unitNormal α) - 1 ≤ coordDot p (unitNormal α)

theorem AngularConstraints.upperCap {S K : Set Plane} {α : ℝ}
    (h : AngularConstraints S K α) (hK : IsCompact K) (hne : K.Nonempty)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) : AngularConstraints S (AmbidextrousSofa.upperCap K) α := by
  have hsin {θ : ℝ} (h0 : 0 < θ) (hθ : θ ≤ α) : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0.le (by linarith [h.angle_le, Real.pi_pos])
  refine ⟨h.angle_pos, h.angle_le, fun θ hθ p hp => ?_, fun p hp => ?_⟩
  · have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, h.angle_le]⟩
    simpa only [canonicalHall, support_upperCap (v := unitNormal θ) hK hne hK0 (hsin hθ.1 hθ.2.le),
      support_upperCap (v := companionNormal θ) hK hne hK0 hc] using h.inside θ hθ hp
  · rw [support_upperCap hK hne hK0 (hsin h.angle_pos le_rfl)]; exact h.terminal p hp

end AmbidextrousSofa

end BPn29

end BP29

section BP30

noncomputable section BPn30

open Set

namespace AmbidextrousSofa.Reference

def referenceSofa : Set Plane :=
  {p | p ∈ referenceHull ∧ referenceNiche p.1 ≤ p.2 ∧ referenceNiche p.1 ≤ 1 - p.2}

theorem referenceSofa_subset_referenceHull : referenceSofa ⊆ referenceHull := fun _ hp => hp.1

theorem isClosed_referenceSofa : IsClosed referenceSofa := by
  have hn : Continuous fun p : Plane => referenceNiche p.1 :=
    continuous_referenceNiche.comp continuous_fst
  exact isClosed_referenceHull.inter ((isClosed_le hn continuous_snd).inter
    (isClosed_le hn (continuous_const.sub continuous_snd)))

theorem isCompact_referenceSofa : IsCompact referenceSofa :=
  isCompact_referenceHull.of_isClosed_subset isClosed_referenceSofa
    referenceSofa_subset_referenceHull

theorem reflect_mem_referenceSofa (p : Plane) : reflect p ∈ referenceSofa ↔ p ∈ referenceSofa := by
  change reflect p ∈ referenceHull ∧ _ ↔ _
  rw [reflect_mem_referenceHull]
  simp only [referenceSofa, mem_ofPred_eq, reflect, sub_sub_cancel, and_comm]

theorem image_reflect_referenceSofa : reflect '' referenceSofa = referenceSofa :=
  (image_reflect_eq_preimage _).trans (ext reflect_mem_referenceSofa)

theorem midline_mem_referenceHull {x : ℝ} (hx : x ∈ horizontalProjection referenceHull) :
    (x, 1 / 2) ∈ referenceHull := by
  obtain ⟨p, hp, rfl⟩ := hx
  convert convex_referenceHull hp ((reflect_mem_referenceHull p).2 hp)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) using 1
  ext <;> simp [reflect] <;> ring

theorem midline_mem_referenceSofa {x : ℝ} (hx : x ∈ horizontalProjection referenceHull) :
    (x, 1 / 2) ∈ referenceSofa :=
  ⟨midline_mem_referenceHull hx, (referenceNiche_lt_half x).le,
    (referenceNiche_lt_half x).le.trans (by norm_num)⟩

theorem center_mem_referenceSofa : center ∈ referenceSofa :=
  midline_mem_referenceSofa ⟨center, center_mem_referenceHull, rfl⟩

theorem vertical_to_midline_mem_referenceSofa {p : Plane} (hp : p ∈ referenceSofa)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (p.1, (1 - t) * p.2 + t * (1 / 2)) ∈ referenceSofa := by
  have h1 := mul_le_mul_of_nonneg_left hp.2.1 (sub_nonneg.2 ht.2)
  have h2 := mul_le_mul_of_nonneg_left hp.2.2 (sub_nonneg.2 ht.2)
  have h3 := mul_le_mul_of_nonneg_left (referenceNiche_lt_half p.1).le ht.1
  exact ⟨convex_verticalFiber convex_referenceHull p.1 hp.1
    (midline_mem_referenceHull ⟨p, hp.1, rfl⟩) (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t),
    by dsimp only; linarith, by dsimp only; linarith⟩

theorem isConnected_referenceSofa : IsConnected referenceSofa := by

  refine IsPathConnected.isConnected ⟨center, center_mem_referenceSofa, fun p hp => ?_⟩
  refine JoinedIn.trans (y := (p.1, 1 / 2)) ?_ (JoinedIn.symm ?_)
  · refine JoinedIn.ofLine (f := fun t : ℝ => ((1 - t) * k + t * p.1, (1 / 2 : ℝ)))
      (by fun_prop) (by simp [center]) (by simp) ?_
    rintro _ ⟨t, ht, rfl⟩
    exact midline_mem_referenceSofa (convex_horizontalProjection convex_referenceHull
      ⟨center, center_mem_referenceHull, rfl⟩ ⟨p, hp.1, rfl⟩ (sub_nonneg.2 ht.2) ht.1
      (sub_add_cancel 1 t))
  · refine JoinedIn.ofLine (f := fun t : ℝ => (p.1, (1 - t) * p.2 + t * (1 / 2)))
      (by fun_prop) (by simp) (by simp) ?_
    rintro _ ⟨t, ht, rfl⟩
    exact vertical_to_midline_mem_referenceSofa hp ht

def lowerReferencePath : RigidMotionPath where
  angle := fun t => -(Real.pi / 2 * t)
  shift := fun t => (1 - referenceF (Real.pi / 2 * t), 1 - referenceG (Real.pi / 2 * t))
  continuous_angle := by fun_prop
  continuous_shift := by
    have hf := continuous_referenceF
    have hg := continuous_referenceG
    fun_prop

theorem quarterAngle_mem {t : ℝ} (ht : t ∈ motionInterval) :
    Real.pi / 2 * t ∈ Icc (0 : ℝ) (Real.pi / 2) :=
  ⟨mul_nonneg (by positivity) ht.1, mul_le_of_le_one_right (by positivity) ht.2⟩

theorem lowerReferencePath_eq_canonical {t : ℝ} (ht : t ∈ motionInterval) (p : Plane) :
    lowerReferencePath.placement t p = canonicalPlacement referenceHull (Real.pi / 2 * t) p := by
  rw [canonicalPlacement_eq_rigidMap, companionNormal_eq_unitNormal, ← angleSupport,
    ← angleSupport, angleSupport_referenceHull_eq_f (quarterAngle_mem ht),
    angleSupport_referenceHull_eq_g (quarterAngle_mem ht)]
  rfl

theorem referenceSofa_subset_canonicalHall {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    referenceSofa ⊆ canonicalHall referenceHull (unitNormal t) (companionNormal t) := by
  intro p hp
  refine (mem_canonicalHall referenceHull _ _ p).2 ⟨coordDot_le_support isCompact_referenceHull
    hp.1 _, coordDot_le_support isCompact_referenceHull hp.1 _, ?_⟩

  have htop : support referenceHull (0, 1) = 1 := by
    simpa [angleSupport, unitNormal, referenceF_pi_div_two] using
      angleSupport_referenceHull_eq_f (t := Real.pi / 2) ⟨by positivity, le_rfl⟩
  have hy := (referenceHull_subset_unitStrip hp.1).1
  rcases ht.1.eq_or_lt with rfl | h0
  · right; simpa [companionNormal, coordDot, htop] using hy
  rcases ht.2.eq_or_lt with rfl | h1
  · left; simpa [unitNormal, coordDot, htop] using hy
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨h0, h1⟩
  refine (cornerWall_le_iff hs hc).1 ?_
  exact (cornerWall_le_sweptNiche (sweptWallValues_bddAbove isCompact_referenceHull le_rfl p.1)
    ⟨h0, h1⟩).trans hp.2.1

theorem lowerReferencePath_start (p : Plane) : lowerReferencePath.placement 0 p = p := by
  simp [lowerReferencePath, RigidMotionPath.placement, referenceF_zero, referenceG_zero,
    Prod.mk_zero_zero, rigidMap_zero_zero]

theorem lowerReferencePath_finish (p : Plane) :
    lowerReferencePath.placement 1 p = (p.2, 2 - 8 / 3 * A - p.1) := by
  ext <;> simp [lowerReferencePath, RigidMotionPath.placement, rigidMap, rotate,
    referenceF_pi_div_two, referenceG_pi_div_two]
  ring

theorem referenceSofa_lowerPassage :
    Passage referenceSofa lowerHall incomingArm lowerOutgoingArm lowerReferencePath := by
  refine ⟨fun t ht => ?_, ?_, ?_⟩ <;> rintro _ ⟨p, hp, rfl⟩ <;>
    have hbox := referenceHull_subset_box hp.1
  · rw [lowerReferencePath_eq_canonical ht]
    exact (canonicalPlacement_mem_lowerHall_iff _ _ _).2
      (referenceSofa_subset_canonicalHall (quarterAngle_mem ht) hp)
  · rw [lowerReferencePath_start]
    exact ⟨hbox.1.2, hbox.2.1, hbox.2.2⟩
  · rw [lowerReferencePath_finish]
    exact ⟨hbox.2.1, hbox.2.2, by linarith [hbox.1.1]⟩

end AmbidextrousSofa.Reference

end BPn30

end BP30

section BP31

noncomputable section BPn31

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

end AmbidextrousSofa

end BPn31

end BP31

section BP32

noncomputable section BPn32

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem absolutelyContinuousOnInterval_const (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval

end AmbidextrousSofa

end BPn32

end BP32

section BP33

noncomputable section BPn33

open Set MeasureTheory

namespace AmbidextrousSofa

def coordDet (p q : Plane) : ℝ := p.1 * q.2 - p.2 * q.1

theorem IsDownwardCap.eq_verticalIntervalRegion {U : Set Plane} (hU : IsDownwardCap U) :
    U = verticalIntervalRegion (Icc (horizontalLeft U) (horizontalRight U))
      (fun _ => 0) (capRoof U) := by
  ext p
  rw [hU.mem_iff_projection_and_roof,
    hU.horizontalProjection_eq_Icc]
  rfl

theorem IsDownwardCap.volumeReal_eq_integral_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) :
    volume.real U = ∫ x in Icc (horizontalLeft U) (horizontalRight U), capRoof U x := by
  have hroof : ∀ x, 0 ≤ capRoof U x := capRoof_nonneg hU.isCompact fun p hp => (hU.inStrip hp).1
  have hvol := volume_verticalIntervalRegion_eq_lintegral (lower := fun _ => 0)
    (I := Icc (horizontalLeft U) (horizontalRight U)) measurableSet_Icc measurable_const
    hU.measurable_capRoof
  rw [← hU.eq_verticalIntervalRegion] at hvol
  simp only [sub_zero, ← ofReal_integral_eq_lintegral_ofReal (hU.integrableOn_capRoof_Icc _ _)
    (.of_forall hroof)] at hvol
  rw [measureReal_def, hvol, ENNReal.toReal_ofReal (integral_nonneg hroof)]

theorem IsDownwardCap.intervalIntegrable_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) (a b : ℝ) : IntervalIntegrable (capRoof U) volume a b :=
  (intervalIntegrable_iff').mpr (hU.integrableOn_capRoof_Icc _ _)

theorem IsDownwardCap.volumeReal_eq_wing_integrals {U : Set Plane}
    (hU : IsDownwardCap U) {l r a b : ℝ}
    (hl : horizontalLeft U = l) (hr : horizontalRight U = r) (hab : a ≤ b)
    (hface : ∀ x ∈ Icc a b, capRoof U x = 1) :
    volume.real U = -(∫ x in a..l, capRoof U x) + (b - a) -
      ∫ x in r..b, capRoof U x := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hU.intervalIntegrable_capRoof l a) (hU.intervalIntegrable_capRoof a r)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hU.intervalIntegrable_capRoof a b) (hU.intervalIntegrable_capRoof b r)
  have h3 : (∫ x in a..b, capRoof U x) = b - a :=
    (intervalIntegral.integral_congr fun x hx => hface x (uIcc_of_le hab ▸ hx)).trans (by simp)
  rw [hU.volumeReal_eq_integral_capRoof, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact),
    hl, hr, intervalIntegral.integral_symm l a, intervalIntegral.integral_symm b r]
  linarith

theorem absolutelyContinuousOnInterval_of_integral_sub
    {f g : ℝ → ℝ} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (heq : ∀ x ∈ uIcc a b, f x - f a = ∫ t in a..x, g t) :
    AbsolutelyContinuousOnInterval f a b :=
  ac_congr ((absolutelyContinuousOnInterval_const (f a) a b).add
    (hg.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc))
    fun x hx => by simp [← heq x hx]

theorem absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hf' : ∀ t, HasDerivWithinAt f (f' t) (Ioi t) t)
    (hi : IntervalIntegrable f' volume a b) : AbsolutelyContinuousOnInterval f a b :=
  absolutelyContinuousOnInterval_of_integral_sub hi fun _ hx =>
    (intervalIntegral.integral_eq_sub_of_hasDeriv_right hf.continuousOn
      (fun t _ => hf' t) (hi.mono_set (uIcc_subset_uIcc_left hx))).symm

theorem ae_hasDerivAt_of_hasDerivWithinAt_Ioi {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hf' : ∀ t, HasDerivWithinAt f (f' t) (Ioi t) t) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (f' t) t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hf.ae_differentiableAt]
    with t ht hd
  have h := (hd (Ioo_subset_Icc_self.trans Icc_subset_uIcc ht)).hasDerivAt
  rwa [(uniqueDiffWithinAt_Ioi t).eq_deriv _ h.hasDerivWithinAt (hf' t)] at h

end AmbidextrousSofa

end BPn33

end BP33

section BP34

noncomputable section BPn34

open Set MeasureTheory

namespace AmbidextrousSofa

end AmbidextrousSofa

end BPn34

end BP34

section BP35

noncomputable section BPn35

open Set MeasureTheory

namespace AmbidextrousSofa

end AmbidextrousSofa

end BPn35

end BP35

section BP36

noncomputable section BPn36

open Set MeasureTheory

namespace AmbidextrousSofa

def roofChord (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  f a + ((f b - f a) / (b - a)) * (x - a)

theorem continuous_roofChord (f : ℝ → ℝ) (a b : ℝ) :
    Continuous (roofChord f a b) := by
  unfold roofChord
  fun_prop

theorem roofChord_left (f : ℝ → ℝ) (a b : ℝ) : roofChord f a b a = f a := by
  simp [roofChord]

theorem roofChord_right (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    roofChord f a b b = f b := by
  rw [roofChord, div_mul_cancel₀ _ (sub_pos.mpr hab).ne']
  ring

theorem roofChord_eq_interpolation (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (x : ℝ) :
    roofChord f a b x = (b - x) / (b - a) * f a + (x - a) / (b - a) * f b := by
  rw [roofChord]
  field_simp [(sub_pos.mpr hab).ne']
  ring

theorem ConcaveOn.roofChord_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) {a b x : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a < b) (hx : x ∈ Icc a b) : roofChord f a b x ≤ f x := by
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have hpoint : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    field_simp
    ring
  rw [roofChord_eq_interpolation f hab]
  simpa only [smul_eq_mul, hpoint] using hf.2 ha hb
    (div_nonneg (sub_nonneg.mpr hx.2) (sub_pos.mpr hab).le)
    (div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le) (by field_simp; ring)

end AmbidextrousSofa

end BPn36

end BP36

section BP37

noncomputable section BPn37

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.continuousOn_capRoof_Icc {U : Set Plane}
    (hU : IsDownwardCap U) :
    ContinuousOn (capRoof U) (Icc (horizontalLeft U) (horizontalRight U)) := by
  rcases (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact).eq_or_lt with heq | hlt
  · rw [heq, Icc_self]
    exact continuousOn_singleton _ _
  have hbelow (x) (hx : x ∈ Icc (horizontalLeft U) (horizontalRight U)) :=
    ConcaveOn.roofChord_le hU.concaveOn_capRoof (horizontalLeft_mem hU.nonempty hU.isCompact)
      (horizontalRight_mem hU.nonempty hU.isCompact) hlt hx

  have hg := continuous_roofChord (capRoof U) (horizontalLeft U) (horizontalRight U)
  have key {x} (hx : roofChord (capRoof U) (horizontalLeft U) (horizontalRight U) x = capRoof U x) :
      ContinuousWithinAt (capRoof U) (Icc (horizontalLeft U) (horizontalRight U)) x :=
    continuousWithinAt_iff_lower_upperSemicontinuousWithinAt.mpr ⟨fun c hc => by
      filter_upwards [hg.continuousAt.continuousWithinAt.lowerSemicontinuousWithinAt c
        (by simpa only [hx] using hc), self_mem_nhdsWithin] with y hy hys
      exact hy.trans_le (hbelow y hys),
      hU.upperSemicontinuous_capRoof.upperSemicontinuousWithinAt _ _⟩
  exact (hU.horizontalProjection_eq_Icc ▸
    hU.concaveOn_capRoof).continuousOn_Icc hlt
    ((continuousWithinAt_Icc_iff_Ici hlt).mp (key (roofChord_left _ _ _)))
    ((continuousWithinAt_Icc_iff_Iic hlt).mp (key (roofChord_right _ hlt)))

theorem IsDownwardCap.continuousOn_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) : ContinuousOn (capRoof U) (horizontalProjection U) :=
  hU.horizontalProjection_eq_Icc ▸ hU.continuousOn_capRoof_Icc

end AmbidextrousSofa

end BPn37

end BP37

section BP38

noncomputable section BPn38

open Set MeasureTheory

namespace AmbidextrousSofa

def innerCornerPoint (f g : ℝ → ℝ) (t : ℝ) : Plane :=
  ((f t - 1) * Real.cos t - (g t - 1) * Real.sin t,
    (f t - 1) * Real.sin t + (g t - 1) * Real.cos t)

def firstTangentPoint (f fD : ℝ → ℝ) (t : ℝ) : Plane :=
  Reference.supportPoint (fun s => f s - 1) fD t

def secondTangentPoint (g gD : ℝ → ℝ) (t : ℝ) : Plane :=
  Reference.companionSupportPoint (fun s => g s - 1) gD t

def supportP (fD g : ℝ → ℝ) (t : ℝ) : ℝ := fD t - g t + 1

def supportQ (gD f : ℝ → ℝ) (t : ℝ) : ℝ := gD t + f t - 1

def supportPointDX (f fDD : ℝ → ℝ) (t : ℝ) : ℝ := -(f t + fDD t) * Real.sin t

def supportPointDY (f fDD : ℝ → ℝ) (t : ℝ) : ℝ := (f t + fDD t) * Real.cos t

def companionSupportPointDX (g gDD : ℝ → ℝ) (t : ℝ) : ℝ := -(g t + gDD t) * Real.cos t

def companionSupportPointDY (g gDD : ℝ → ℝ) (t : ℝ) : ℝ := -(g t + gDD t) * Real.sin t

theorem companionSupportPoint_coordinates (g gD : ℝ → ℝ) (t : ℝ) :
    Reference.companionSupportPoint g gD t =
      (-g t * Real.sin t - gD t * Real.cos t,
        g t * Real.cos t - gD t * Real.sin t) := by
  simp [Reference.companionSupportPoint, Reference.supportPoint, rotate]
  ring

theorem coordDet_supportPoint (f fD fDD : ℝ → ℝ) (t : ℝ) :
    coordDet (Reference.supportPoint f fD t)
      (supportPointDX f fDD t, supportPointDY f fDD t) = f t * (f t + fDD t) := by
  simp only [coordDet, Reference.supportPoint, supportPointDX, supportPointDY]
  linear_combination f t * (f t + fDD t) * Real.sin_sq_add_cos_sq t

theorem coordDet_companionSupportPoint (g gD gDD : ℝ → ℝ) (t : ℝ) :
    coordDet (Reference.companionSupportPoint g gD t)
      (companionSupportPointDX g gDD t, companionSupportPointDY g gDD t) =
      g t * (g t + gDD t) := by
  simp only [companionSupportPoint_coordinates, coordDet, companionSupportPointDX,
    companionSupportPointDY]
  linear_combination g t * (g t + gDD t) * Real.sin_sq_add_cos_sq t

theorem IsDownwardCap.capRoof_eq_of_support_eq {U : Set Plane} (hU : IsDownwardCap U)
    {p : Plane} (hp : p ∈ U) {θ : ℝ} (hsin : 0 < Real.sin θ)
    (hsupport : coordDot p (unitNormal θ) = support U (unitNormal θ)) :
    capRoof U p.1 = p.2 := by
  refine le_antisymm ?_ (le_capRoof hU.isCompact hp)
  have h := hsupport ▸ coordDot_le_support hU.isCompact
    (capRoof_mem hU.isCompact (mem_image_of_mem Prod.fst hp)) (unitNormal θ)
  simp only [coordDot, unitNormal] at h
  exact le_of_mul_le_mul_right (by linarith) hsin

end AmbidextrousSofa

end BPn38

end BP38

section BP39

noncomputable section BPn39

open Set MeasureTheory

namespace AmbidextrousSofa

theorem firstTangent_dominates_support {f fD fDD : ℝ → ℝ}
    (hf : Continuous f) (hfD : Continuous fD)
    (hderiv : ∀ t, HasDerivWithinAt f (fD t) (Ioi t) t)
    (hsecond : ∀ t, HasDerivWithinAt fD (fDD t) (Ioi t) t)
    (hcurv : ∀ t ∈ Icc 0 (Real.pi / 2), f t + fDD t ≤ 1)
    {s t : ℝ} (hs : s ∈ Icc 0 (Real.pi / 2)) (ht : t ∈ Icc 0 (Real.pi / 2)) :
    f t - 1 ≤ coordDot (firstTangentPoint f fD s) (unitNormal t) := by
  have h := Reference.supportProjection_le_self (h := fun x => 1 - f x) (hD := fun x => -fD x)
    (hDD := fun x => -fDD x) (continuous_const.sub hf) hfD.neg
    (fun x => (hderiv x).const_sub 1) (fun x => (hsecond x).neg)
    (fun x hx => by linarith [hcurv x hx]) (by linarith [Real.pi_pos]) hs ht
  rw [firstTangentPoint, Reference.coordDot_supportPoint]
  simp only [Reference.supportProjection] at h ⊢
  linarith

theorem secondTangent_dominates_support {g gD gDD : ℝ → ℝ}
    (hg : Continuous g) (hgD : Continuous gD)
    (hderiv : ∀ t, HasDerivWithinAt g (gD t) (Ioi t) t)
    (hsecond : ∀ t, HasDerivWithinAt gD (gDD t) (Ioi t) t)
    (hcurv : ∀ t ∈ Icc 0 (Real.pi / 2), g t + gDD t ≤ 1)
    {s t : ℝ} (hs : s ∈ Icc 0 (Real.pi / 2)) (ht : t ∈ Icc 0 (Real.pi / 2)) :
    g t - 1 ≤ coordDot (secondTangentPoint g gD s) (companionNormal t) := by
  rw [secondTangentPoint, companionNormal_eq_unitNormal, Reference.coordDot_companionSupportPoint,
    add_sub_cancel_right, ← Reference.coordDot_supportPoint]
  exact firstTangent_dominates_support hg hgD hderiv hsecond hcurv hs ht

theorem innerCorner_dot_eq_firstTangent (f g fD : ℝ → ℝ) (s t : ℝ) :
    coordDot (innerCornerPoint f g s) (unitNormal t) =
      coordDot (firstTangentPoint f fD s) (unitNormal t) -
        supportP fD g s * Real.sin (t - s) := by
  unfold coordDot innerCornerPoint firstTangentPoint Reference.supportPoint unitNormal supportP
  rw [Real.sin_sub]
  ring

theorem innerCorner_dot_eq_secondTangent (f g gD : ℝ → ℝ) (s t : ℝ) :
    coordDot (innerCornerPoint f g s) (companionNormal t) =
      coordDot (secondTangentPoint g gD s) (companionNormal t) +
        supportQ gD f s * Real.sin (s - t) := by
  rw [secondTangentPoint, companionSupportPoint_coordinates]
  unfold coordDot innerCornerPoint companionNormal supportQ
  rw [Real.sin_sub]
  ring

theorem innerCorner_snd_eq_firstTangent (f g fD : ℝ → ℝ) (s : ℝ) :
    (innerCornerPoint f g s).2 = (firstTangentPoint f fD s).2 -
      supportP fD g s * Real.cos s := by
  unfold innerCornerPoint firstTangentPoint Reference.supportPoint supportP
  ring

theorem sweptNiche_eq_of_global_contact {U : Set Plane} (hU : IsCompact U) {f g : ℝ → ℝ}
    (hF : ∀ t ∈ Icc 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hG : ∀ t ∈ Icc 0 (Real.pi / 2), support U (companionNormal t) = g t)
    {p : Plane} (hp : 0 ≤ p.2)
    (hbound : ∀ t ∈ Ioo 0 (Real.pi / 2),
      f t - 1 ≤ coordDot p (unitNormal t) ∨ g t - 1 ≤ coordDot p (companionNormal t))
    {s : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2)) (h1 : coordDot p (unitNormal s) ≤ f s - 1)
    (h2 : coordDot p (companionNormal s) ≤ g s - 1) :
    sweptNiche U (Real.pi / 2) p.1 = p.2 := by
  have hsc : ∀ t ∈ Ioo 0 (Real.pi / 2), 0 < Real.sin t ∧ 0 < Real.cos t := fun t ht =>
    sin_cos_pos_of_mem_quarter ht
  refine le_antisymm (sweptNiche_le_of_forall (by positivity) hp fun t ht => ?_)
    (le_trans ?_ (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU le_rfl p.1) hs))
  · rw [cornerWall_le_iff (hsc t ht).1 (hsc t ht).2, hF t (Ioo_subset_Icc_self ht),
      hG t (Ioo_subset_Icc_self ht)]
    exact hbound t ht
  · have := hF s (Ioo_subset_Icc_self hs)
    have := hG s (Ioo_subset_Icc_self hs)
    simp only [coordDot, unitNormal, companionNormal] at h1 h2
    exact le_min ((le_div_iff₀ (hsc s hs).1).2 (by linarith))
      ((le_div_iff₀ (hsc s hs).2).2 (by linarith))

theorem sweptNiche_firstTangent {U : Set Plane} (hU : IsCompact U)
    {f g fD : ℝ → ℝ} (hF : ∀ t ∈ Icc 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hG : ∀ t ∈ Icc 0 (Real.pi / 2), support U (companionNormal t) = g t)
    (hFtop : f (Real.pi / 2) = 1) {s : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2))
    (hp : supportP fD g s ≤ 0)
    (hdom : ∀ t ∈ Icc 0 (Real.pi / 2),
      f t - 1 ≤ coordDot (firstTangentPoint f fD s) (unitNormal t)) :
    sweptNiche U (Real.pi / 2) (firstTangentPoint f fD s).1 =
      (firstTangentPoint f fD s).2 := by
  refine sweptNiche_eq_of_global_contact hU hF hG ?_
    (fun t ht => .inl (hdom t (Ioo_subset_Icc_self ht))) hs ?_ ?_
  · simpa [hFtop, coordDot, unitNormal] using hdom _ ⟨by positivity, le_rfl⟩
  · rw [firstTangentPoint, Reference.coordDot_supportPoint, Reference.supportProjection_self]
  · rw [firstTangentPoint, companionNormal_eq_unitNormal, Reference.coordDot_supportPoint]
    simp [Reference.supportProjection]
    linarith [show fD s - g s + 1 ≤ 0 from hp]

theorem sweptNiche_secondTangent {U : Set Plane} (hU : IsCompact U)
    {f g gD : ℝ → ℝ} (hF : ∀ t ∈ Icc 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hG : ∀ t ∈ Icc 0 (Real.pi / 2), support U (companionNormal t) = g t)
    (hGtop : g 0 = 1) {s : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2))
    (hq : 0 ≤ supportQ gD f s)
    (hdom : ∀ t ∈ Icc 0 (Real.pi / 2),
      g t - 1 ≤ coordDot (secondTangentPoint g gD s) (companionNormal t)) :
    sweptNiche U (Real.pi / 2) (secondTangentPoint g gD s).1 =
      (secondTangentPoint g gD s).2 := by
  refine sweptNiche_eq_of_global_contact hU hF hG ?_
    (fun t ht => .inr (hdom t (Ioo_subset_Icc_self ht))) hs ?_ ?_
  · simpa [hGtop, coordDot, companionNormal] using hdom 0 ⟨le_rfl, by positivity⟩
  · rw [secondTangentPoint, Reference.coordDot_companionSupportPoint]
    simp [Reference.supportProjection]
    linarith [show 0 ≤ gD s + f s - 1 from hq]
  · rw [secondTangentPoint, companionNormal_eq_unitNormal, Reference.coordDot_companionSupportPoint,
      add_sub_cancel_right, Reference.supportProjection_self]

theorem sweptNiche_innerCorner {U : Set Plane} (hU : IsCompact U)
    {f g fD gD : ℝ → ℝ}
    (hF : ∀ t ∈ Icc 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hG : ∀ t ∈ Icc 0 (Real.pi / 2), support U (companionNormal t) = g t)
    (hFtop : f (Real.pi / 2) = 1) {s : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2))
    (hp : supportP fD g s ≤ 0) (hq : 0 ≤ supportQ gD f s)
    (hB : ∀ t ∈ Icc 0 (Real.pi / 2),
      f t - 1 ≤ coordDot (firstTangentPoint f fD s) (unitNormal t))
    (hD : ∀ t ∈ Icc 0 (Real.pi / 2),
      g t - 1 ≤ coordDot (secondTangentPoint g gD s) (companionNormal t)) :
    sweptNiche U (Real.pi / 2) (innerCornerPoint f g s).1 = (innerCornerPoint f g s).2 := by
  refine sweptNiche_eq_of_global_contact hU hF hG ?_ (fun t ht => ?_) hs ?_ ?_
  · have := hB _ ⟨by positivity, le_rfl⟩
    simp [hFtop, coordDot, unitNormal] at this
    rw [innerCorner_snd_eq_firstTangent f g fD]
    nlinarith [(sin_cos_pos_of_mem_quarter hs).2]
  · rcases le_total s t with hst | hts
    · refine .inl ?_
      rw [innerCorner_dot_eq_firstTangent f g fD]
      nlinarith [hB t (Ioo_subset_Icc_self ht), Real.sin_nonneg_of_nonneg_of_le_pi
        (sub_nonneg.mpr hst) (by linarith [ht.2, hs.1, Real.pi_pos])]
    · refine .inr ?_
      rw [innerCorner_dot_eq_secondTangent f g gD]
      nlinarith [hD t (Ioo_subset_Icc_self ht), Real.sin_nonneg_of_nonneg_of_le_pi
        (sub_nonneg.mpr hts) (by linarith [hs.2, ht.1, Real.pi_pos])]
  · refine le_of_eq ?_
    simp only [coordDot, innerCornerPoint, unitNormal]
    linear_combination (f s - 1) * Real.sin_sq_add_cos_sq s
  · refine le_of_eq ?_
    simp only [coordDot, innerCornerPoint, companionNormal]
    linear_combination (g s - 1) * Real.sin_sq_add_cos_sq s

end AmbidextrousSofa

end BPn39

end BP39

section BP40

noncomputable section BPn40

open Set MeasureTheory

namespace AmbidextrousSofa

def innerCornerDX (f g fD gD : ℝ → ℝ) (t : ℝ) : ℝ :=
  supportP fD g t * Real.cos t - supportQ gD f t * Real.sin t

def innerCornerDY (f g fD gD : ℝ → ℝ) (t : ℝ) : ℝ :=
  supportP fD g t * Real.sin t + supportQ gD f t * Real.cos t

def cornerDensity (f g fD gD : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t - 1) * supportQ gD f t - (g t - 1) * supportP fD g t

def firstMomentumPrimitive (f g fD : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t - 1) * supportP fD g t

def secondMomentumPrimitive (f g gD : ℝ → ℝ) (t : ℝ) : ℝ :=
  (g t - 1) * supportQ gD f t

def firstMomentumDerivative (f g fD gD fDD : ℝ → ℝ) (t : ℝ) : ℝ :=
  fD t * supportP fD g t + (f t - 1) * (fDD t - gD t)

def secondMomentumDerivative (f g fD gD gDD : ℝ → ℝ) (t : ℝ) : ℝ :=
  gD t * supportQ gD f t + (g t - 1) * (gDD t + fD t)

theorem coordDet_innerCorner (f g fD gD : ℝ → ℝ) (t : ℝ) :
    coordDet (innerCornerPoint f g t)
      (innerCornerDX f g fD gD t, innerCornerDY f g fD gD t) =
      cornerDensity f g fD gD t := by
  simp only [coordDet, innerCornerPoint, innerCornerDX, innerCornerDY, cornerDensity]
  linear_combination ((f t - 1) * supportQ gD f t - (g t - 1) * supportP fD g t) *
    Real.sin_sq_add_cos_sq t

theorem innerCorner_eq_firstTangent_of_momentum_zero
    {f g fD : ℝ → ℝ} {t : ℝ} (hp : supportP fD g t = 0) :
    innerCornerPoint f g t = firstTangentPoint f fD t := by
  rw [innerCornerPoint, firstTangentPoint, Reference.supportPoint,
    show fD t = g t - 1 by unfold supportP at hp; linarith]

theorem innerCorner_eq_secondTangent_of_momentum_zero
    {f g gD : ℝ → ℝ} {t : ℝ} (hq : supportQ gD f t = 0) :
    innerCornerPoint f g t = secondTangentPoint g gD t := by
  rw [secondTangentPoint, companionSupportPoint_coordinates, innerCornerPoint,
    show gD t = -(f t - 1) by unfold supportQ at hq; linarith]
  ext <;> dsimp <;> ring

theorem firstTangent_density_identity (f g fD gD fDD : ℝ → ℝ) (t : ℝ) :
    (f t - 1) * (f t - 1 + fDD t) = cornerDensity f g fD gD t -
      supportP fD g t ^ 2 + firstMomentumDerivative f g fD gD fDD t := by
  unfold cornerDensity firstMomentumDerivative supportP supportQ
  ring

theorem secondTangent_density_identity (f g fD gD gDD : ℝ → ℝ) (t : ℝ) :
    (g t - 1) * (g t - 1 + gDD t) = cornerDensity f g fD gD t -
      supportQ gD f t ^ 2 + secondMomentumDerivative f g fD gD gDD t := by
  unfold cornerDensity secondMomentumDerivative supportP supportQ
  ring

theorem integral_density_of_identity {a b m : ℝ} {L c P M : ℝ → ℝ}
    (hid : ∀ t, L t = c t - P t ^ 2 + M t) (hc : Continuous c) (hP : Continuous P)
    (hMi : IntervalIntegrable M volume a b) (hftc : ∫ t in a..b, M t = m) :
    (∫ t in a..b, L t) = (∫ t in a..b, c t) - (∫ t in a..b, P t ^ 2) + m := by
  have hc' := hc.intervalIntegrable (μ := volume) a b
  have hP' : IntervalIntegrable (fun t => P t ^ 2) volume a b := (hP.pow 2).intervalIntegrable a b
  rw [intervalIntegral.integral_congr fun t _ => hid t,
    intervalIntegral.integral_add (hc'.sub hP') hMi, intervalIntegral.integral_sub hc' hP', hftc]

theorem integral_split_of_eqOn {a b c : ℝ} {F G H : ℝ → ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hF : Continuous F) (hG : EqOn F G (Icc a b)) (hH : EqOn F H (Icc b c)) :
    (∫ t in a..c, F t) = (∫ t in a..b, G t) + ∫ t in b..c, H t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable a b)
    (hF.intervalIntegrable b c)]
  exact congrArg₂ (· + ·) (intervalIntegral.integral_congr (uIcc_of_le hab ▸ hG))
    (intervalIntegral.integral_congr (uIcc_of_le hbc ▸ hH))

theorem integral_min_sq_of_sign_switch {a b c : ℝ} {p : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hp : Continuous p)
    (hleft : ∀ t ∈ Icc a b, 0 ≤ p t) (hright : ∀ t ∈ Icc b c, p t ≤ 0) :
    (∫ t in a..c, min (p t) 0 ^ 2) = ∫ t in b..c, p t ^ 2 := by
  rw [integral_split_of_eqOn (F := fun t => min (p t) 0 ^ 2) (G := 0) (H := fun t => p t ^ 2)
    hab hbc ((hp.min continuous_const).pow 2) (fun t ht => by simp [min_eq_right (hleft t ht)])
    fun t ht => by simp [min_eq_left (hright t ht)]]
  simp

theorem integral_max_sq_of_sign_switch {a b c : ℝ} {q : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hq : Continuous q)
    (hleft : ∀ t ∈ Icc a b, 0 ≤ q t) (hright : ∀ t ∈ Icc b c, q t ≤ 0) :
    (∫ t in a..c, max (q t) 0 ^ 2) = ∫ t in a..b, q t ^ 2 := by
  rw [integral_split_of_eqOn (F := fun t => max (q t) 0 ^ 2) (G := fun t => q t ^ 2) (H := 0)
    hab hbc ((hq.max continuous_const).pow 2) (fun t ht => by simp [max_eq_left (hleft t ht)])
    fun t ht => by simp [max_eq_right (hright t ht)]]
  simp

end AmbidextrousSofa

end BPn40

end BP40

section BP41

noncomputable section BPn41

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem integral_eq_sub_of_ac_of_ae_hasDerivAt
    {a b : ℝ} {E D : ℝ → ℝ} (hab : a ≤ b)
    (hE : AbsolutelyContinuousOnInterval E a b)
    (hD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt E (D t) t) :
    (∫ t in a..b, D t) = E b - E a := by
  refine (intervalIntegral.integral_congr_ae_restrict ?_).trans hE.integral_deriv_eq_sub
  rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
  exact hD.mono fun _ h => h.deriv.symm

theorem integral_graph_parametrization_ac {a b : ℝ} {F X Y XD : ℝ → ℝ}
    (hab : a ≤ b) (hX : AbsolutelyContinuousOnInterval X a b)
    (hXD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt X (XD t) t)
    (hF : ContinuousOn F (X '' Icc a b))
    (hgraph : ∀ t ∈ Ioo a b, F (X t) = Y t) :
    (∫ x in X a..X b, F x) = ∫ t in a..b, Y t * XD t := by
  have hS : IsCompact (X '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn (uIcc_of_le hab ▸ hX.continuousOn)
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hS.isClosed ⟨_, hF.domRestrict⟩
  have hGF : EqOn G F (X '' Icc a b) := fun x hx => congrArg (· ⟨x, hx⟩) hG
  have hP (x : ℝ) : HasDerivAt (fun x => ∫ s in X a..x, G s) (G x) x :=
    (G.continuous.integral_hasStrictDerivAt (X a) x).hasDerivAt
  have hC : ContDiff ℝ 1 fun x => ∫ s in X a..x, G s := contDiff_one_iff_deriv.2
    ⟨fun x => (hP x).differentiableAt, by rw [funext fun x => (hP x).deriv]; exact G.continuous⟩
  obtain ⟨L, hL⟩ := hC.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
  have h := integral_eq_sub_of_ac_of_ae_hasDerivAt hab
    (ac_comp_lip hL (uIcc_of_le hab ▸ mapsTo_image X _) hX)
    (hXD.mono fun t ht => (hP (X t)).comp t ht)
  simp only [Function.comp_apply, intervalIntegral.integral_same, sub_zero] at h
  calc (∫ x in X a..X b, F x) = ∫ x in X a..X b, G x := intervalIntegral.integral_congr
        fun x hx => (hGF (uIcc_of_le hab ▸ intermediate_value_uIcc hX.continuousOn hx)).symm
    _ = ∫ t in a..b, Y t * XD t := h.symm.trans <| intervalIntegral.integral_congr_Ioo_of_le hab
        fun t ht => by simp only [hGF (mem_image_of_mem X (Ioo_subset_Icc_self ht)), hgraph t ht]

theorem twice_integral_graph_parametrization_ac
    {a b : ℝ} {F X Y XD YD : ℝ → ℝ}
    (hab : a ≤ b) (hX : AbsolutelyContinuousOnInterval X a b)
    (hY : AbsolutelyContinuousOnInterval Y a b)
    (hXD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt X (XD t) t)
    (hYD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt Y (YD t) t)
    (hXDi : IntervalIntegrable XD volume a b) (hYDi : IntervalIntegrable YD volume a b)
    (hF : ContinuousOn F (X '' Icc a b))
    (hgraph : ∀ t ∈ Ioo a b, F (X t) = Y t) :
    2 * (∫ x in X a..X b, F x) = X b * Y b - X a * Y a -
      ∫ t in a..b, coordDet (X t, Y t) (XD t, YD t) := by
  have hXY := hYDi.continuousOn_mul hX.continuousOn
  have hYX := hXDi.continuousOn_mul hY.continuousOn
  have hparts := integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hX.fun_mul hY)
    ((hXD.and hYD).mono fun t h => h.1.mul h.2)
  rw [intervalIntegral.integral_add (hXDi.mul_continuousOn hY.continuousOn) hXY] at hparts
  simp only [coordDet, intervalIntegral.integral_sub hXY hYX, mul_comm (XD _),
    integral_graph_parametrization_ac hab hX hXD hF hgraph] at hparts ⊢
  linarith

theorem hasDerivAt_supportPoint_fst {f fD : ℝ → ℝ} {fDD t : ℝ}
    (hf : HasDerivAt f (fD t) t) (hfD : HasDerivAt fD fDD t) :
    HasDerivAt (fun s => (Reference.supportPoint f fD s).1)
      (-(f t + fDD) * Real.sin t) t :=
  ((hf.mul (Real.hasDerivAt_cos t)).sub (hfD.mul (Real.hasDerivAt_sin t))).congr_deriv (by ring)

theorem hasDerivAt_supportPoint_snd {f fD : ℝ → ℝ} {fDD t : ℝ}
    (hf : HasDerivAt f (fD t) t) (hfD : HasDerivAt fD fDD t) :
    HasDerivAt (fun s => (Reference.supportPoint f fD s).2)
      ((f t + fDD) * Real.cos t) t :=
  ((hf.mul (Real.hasDerivAt_sin t)).add (hfD.mul (Real.hasDerivAt_cos t))).congr_deriv (by ring)

theorem hasDerivAt_companionSupportPoint_fst {g gD : ℝ → ℝ} {gDD t : ℝ}
    (hg : HasDerivAt g (gD t) t) (hgD : HasDerivAt gD gDD t) :
    HasDerivAt (fun s => (Reference.companionSupportPoint g gD s).1)
      (-(g t + gDD) * Real.cos t) t := by
  simpa only [Reference.companionSupportPoint, rotate, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_mul, one_mul, zero_sub, neg_mul] using
    (hasDerivAt_supportPoint_snd hg hgD).fun_neg

theorem hasDerivAt_companionSupportPoint_snd {g gD : ℝ → ℝ} {gDD t : ℝ}
    (hg : HasDerivAt g (gD t) t) (hgD : HasDerivAt gD gDD t) :
    HasDerivAt (fun s => (Reference.companionSupportPoint g gD s).2)
      (-(g t + gDD) * Real.sin t) t := by
  simpa only [Reference.companionSupportPoint, rotate, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_mul, one_mul, add_zero] using
    hasDerivAt_supportPoint_fst hg hgD

theorem absolutelyContinuousOnInterval_supportPoint
    {a b : ℝ} {f fD : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hfD : AbsolutelyContinuousOnInterval fD a b) :
    AbsolutelyContinuousOnInterval (fun t => (Reference.supportPoint f fD t).1) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (Reference.supportPoint f fD t).2) a b := by
  have hc := Real.contDiff_cos.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)
  have hs := Real.contDiff_sin.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)
  exact ⟨(hf.fun_mul hc).sub (hfD.fun_mul hs), (hf.fun_mul hs).add (hfD.fun_mul hc)⟩

theorem absolutelyContinuousOnInterval_companionSupportPoint
    {a b : ℝ} {g gD : ℝ → ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b) (hgD : AbsolutelyContinuousOnInterval gD a b) :
    AbsolutelyContinuousOnInterval (fun t => (Reference.companionSupportPoint g gD t).1) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (Reference.companionSupportPoint g gD t).2) a b := by
  obtain ⟨h1, h2⟩ := absolutelyContinuousOnInterval_supportPoint hg hgD
  exact ⟨ac_congr h2.neg fun t _ => by simp [Reference.companionSupportPoint, rotate],
    ac_congr h1 fun t _ => by simp [Reference.companionSupportPoint, rotate]⟩

theorem support_energy_graph_identity_ac
    {a b : ℝ} {F X Y XD YD f fD fDD : ℝ → ℝ}
    (hab : a ≤ b) (hX : AbsolutelyContinuousOnInterval X a b)
    (hY : AbsolutelyContinuousOnInterval Y a b)
    (hXD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt X (XD t) t)
    (hYD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt Y (YD t) t)
    (hXDi : IntervalIntegrable XD volume a b) (hYDi : IntervalIntegrable YD volume a b)
    (hF : ContinuousOn F (X '' Icc a b))
    (hgraph : ∀ t ∈ Ioo a b, F (X t) = Y t)
    (hf : AbsolutelyContinuousOnInterval f a b) (hfD : AbsolutelyContinuousOnInterval fD a b)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (fD t) t)
    (hsecond : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt fD (fDD t) t)
    (hfDD : IntervalIntegrable fDD volume a b)
    (hdet : ∀ t ∈ Ioo a b, coordDet (X t, Y t) (XD t, YD t) = f t * (f t + fDD t)) :
    2 * (∫ x in X a..X b, F x) =
      (X b * Y b - f b * fD b) - (X a * Y a - f a * fD a) -
        ∫ t in a..b, f t ^ 2 - fD t ^ 2 := by
  have hdensity : ∫ t in a..b, coordDet (X t, Y t) (XD t, YD t) =
      ∫ t in a..b, (f t ^ 2 - fD t ^ 2) + (fD t * fD t + f t * fDD t) :=
    intervalIntegral.integral_congr_Ioo_of_le hab fun t ht => by rw [hdet t ht]; ring
  rw [intervalIntegral.integral_add
    ((hf.continuousOn.fun_pow 2).fun_sub (hfD.continuousOn.fun_pow 2)).intervalIntegrable
    ((hfD.continuousOn.fun_mul hfD.continuousOn).intervalIntegrable.add
      (hfDD.continuousOn_mul hf.continuousOn)),
    integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hf.fun_mul hfD)
      ((hderiv.and hsecond).mono fun t h => h.1.mul h.2)] at hdensity
  linarith [twice_integral_graph_parametrization_ac hab hX hY hXD hYD hXDi hYDi hF hgraph]

theorem IsDownwardCap.volumeReal_eq_support_energy_ac
    {U : Set Plane} (hU : IsDownwardCap U) {f g fD gD fDD gDD : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 (Real.pi / 2))
    (hg : AbsolutelyContinuousOnInterval g 0 (Real.pi / 2))
    (hfD : AbsolutelyContinuousOnInterval fD 0 (Real.pi / 2))
    (hgD : AbsolutelyContinuousOnInterval gD 0 (Real.pi / 2))
    (hderivF : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)), HasDerivAt f (fD t) t)
    (hderivG : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)), HasDerivAt g (gD t) t)
    (hsecondF : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)), HasDerivAt fD (fDD t) t)
    (hsecondG : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)), HasDerivAt gD (gDD t) t)
    (hfDD : IntervalIntegrable fDD volume 0 (Real.pi / 2))
    (hgDD : IntervalIntegrable gDD volume 0 (Real.pi / 2))
    (hFpoints : ∀ t ∈ Icc 0 (Real.pi / 2), Reference.supportPoint f fD t ∈ U)
    (hGpoints : ∀ t ∈ Icc 0 (Real.pi / 2), Reference.companionSupportPoint g gD t ∈ U)
    (hFsupport : ∀ t ∈ Ioo 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hGsupport : ∀ t ∈ Ioo 0 (Real.pi / 2),
      support U (unitNormal (t + Real.pi / 2)) = g t)
    (hleft : horizontalLeft U = -g (Real.pi / 2)) (hright : horizontalRight U = f 0)
    (hFtop : f (Real.pi / 2) = 1) (hGtop : g 0 = 1)
    (hfaceOrder : -gD 0 ≤ -fD (Real.pi / 2))
    (hface : ∀ x ∈ Icc (-gD 0) (-fD (Real.pi / 2)), capRoof U x = 1) :
    volume.real U = 1 / 2 * ∫ t in (0 : ℝ)..(Real.pi / 2),
      (f t ^ 2 - fD t ^ 2) + (g t ^ 2 - gD t ^ 2) := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hFc := absolutelyContinuousOnInterval_supportPoint hf hfD
  have hGc := absolutelyContinuousOnInterval_companionSupportPoint hg hgD
  have hFrho := hf.continuousOn.intervalIntegrable.add hfDD
  have hGrho := hg.continuousOn.intervalIntegrable.add hgDD
  have hFenergy := support_energy_graph_identity_ac hL hFc.1 hFc.2
    ((hderivF.and hsecondF).mono fun t h => hasDerivAt_supportPoint_fst h.1 h.2)
    ((hderivF.and hsecondF).mono fun t h => hasDerivAt_supportPoint_snd h.1 h.2)
    (hFrho.neg.mul_continuousOn Real.continuous_sin.continuousOn)
    (hFrho.mul_continuousOn Real.continuous_cos.continuousOn)
    (hU.continuousOn_capRoof.mono (image_subset_iff.2 fun t ht =>
      mem_image_of_mem Prod.fst (hFpoints t ht)))
    (fun t ht => hU.capRoof_eq_of_support_eq (hFpoints t (Ioo_subset_Icc_self ht))
      (sin_cos_pos_of_mem_quarter ht).1
      (by rw [Reference.coordDot_supportPoint, Reference.supportProjection_self, hFsupport t ht]))
    hf hfD hderivF hsecondF hfDD (fun t _ => coordDet_supportPoint f fD fDD t)
  have hGenergy := support_energy_graph_identity_ac hL hGc.1 hGc.2
    ((hderivG.and hsecondG).mono fun t h => hasDerivAt_companionSupportPoint_fst h.1 h.2)
    ((hderivG.and hsecondG).mono fun t h => hasDerivAt_companionSupportPoint_snd h.1 h.2)
    (hGrho.neg.mul_continuousOn Real.continuous_cos.continuousOn)
    (hGrho.neg.mul_continuousOn Real.continuous_sin.continuousOn)
    (hU.continuousOn_capRoof.mono (image_subset_iff.2 fun t ht =>
      mem_image_of_mem Prod.fst (hGpoints t ht)))
    (fun t ht => hU.capRoof_eq_of_support_eq (θ := t + Real.pi / 2)
      (hGpoints t (Ioo_subset_Icc_self ht))
      (Real.sin_add_pi_div_two t ▸
        (sin_cos_pos_of_mem_quarter ht).2)
      (by rw [Reference.coordDot_companionSupportPoint, add_sub_cancel_right,
        Reference.supportProjection_self, hGsupport t ht]))
    hg hgD hderivG hsecondG hgDD (fun t _ => coordDet_companionSupportPoint g gD gDD t)
  simp only [Reference.supportPoint, companionSupportPoint_coordinates, Real.cos_zero,
    Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two, hFtop, hGtop, mul_one, mul_zero,
    sub_zero, zero_sub] at hFenergy hGenergy
  rw [intervalIntegral.integral_add
    ((hf.continuousOn.fun_pow 2).fun_sub (hfD.continuousOn.fun_pow 2)).intervalIntegrable
    ((hg.continuousOn.fun_pow 2).fun_sub (hgD.continuousOn.fun_pow 2)).intervalIntegrable]
  linarith [hU.volumeReal_eq_wing_integrals hleft hright hfaceOrder hface]

end AmbidextrousSofa

end BPn41

end BP41

section BP42

noncomputable section BPn42

open Set MeasureTheory

namespace AmbidextrousSofa

theorem signedRoof_integral_of_graphs_ac
    {b d : ℝ} {N f g fD gD fDD gDD : ℝ → ℝ}
    (hb0 : 0 ≤ b) (hbd : b ≤ d) (hdL : d ≤ Real.pi / 2)
    (hN : Continuous N) (hf : Continuous f) (hg : Continuous g)
    (hfD : Continuous fD) (hgD : Continuous gD)
    (hfAC : AbsolutelyContinuousOnInterval f 0 (Real.pi / 2))
    (hgAC : AbsolutelyContinuousOnInterval g 0 (Real.pi / 2))
    (hfDAC : AbsolutelyContinuousOnInterval fD 0 (Real.pi / 2))
    (hgDAC : AbsolutelyContinuousOnInterval gD 0 (Real.pi / 2))
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      HasDerivAt f (fD t) t ∧ HasDerivAt g (gD t) t ∧
      HasDerivAt fD (fDD t) t ∧ HasDerivAt gD (gDD t) t)
    (hfDD : IntervalIntegrable fDD volume 0 (Real.pi / 2))
    (hgDD : IntervalIntegrable gDD volume 0 (Real.pi / 2))
    (hFtop : f (Real.pi / 2) = 1) (hGtop : g 0 = 1)
    (hpzero : supportP fD g b = 0) (hqzero : supportQ gD f d = 0)
    (hgraphD : ∀ t ∈ Ioo 0 d,
      N (secondTangentPoint g gD t).1 = (secondTangentPoint g gD t).2)
    (hgraphC : ∀ t ∈ Ioo b d,
      N (innerCornerPoint f g t).1 = (innerCornerPoint f g t).2)
    (hgraphB : ∀ t ∈ Ioo b (Real.pi / 2),
      N (firstTangentPoint f fD t).1 = (firstTangentPoint f fD t).2) :
    2 * (∫ x in (-gD 0)..(-fD (Real.pi / 2)), N x) =
      -(∫ t in (0 : ℝ)..(Real.pi / 2), cornerDensity f g fD gD t) +
      (∫ t in b..(Real.pi / 2), supportP fD g t ^ 2) +
      ∫ t in (0 : ℝ)..d, supportQ gD f t ^ 2 := by
  have h0d : 0 ≤ d := hb0.trans hbd
  have hbL : b ≤ Real.pi / 2 := hbd.trans hdL
  have hsubD : uIcc 0 d ⊆ uIcc 0 (Real.pi / 2) :=
    uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le h0d hdL)
  have hsubC : uIcc b d ⊆ uIcc 0 (Real.pi / 2) :=
    uIcc_subset_uIcc (mem_uIcc_of_le hb0 hbL) (mem_uIcc_of_le h0d hdL)
  have hsubB : uIcc b (Real.pi / 2) ⊆ uIcc 0 (Real.pi / 2) :=
    uIcc_subset_uIcc (mem_uIcc_of_le hb0 hbL) right_mem_uIcc
  have hderivD := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hdL) hderiv
  have hderivC := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hb0 hdL) hderiv
  have hderivB := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hb0 le_rfl) hderiv
  have hconst := absolutelyContinuousOnInterval_const 1 0 (Real.pi / 2)
  have hsin : AbsolutelyContinuousOnInterval Real.sin 0 (Real.pi / 2) :=
    Real.contDiff_sin.contDiffOn.absolutelyContinuousOnInterval
  have hcos : AbsolutelyContinuousOnInterval Real.cos 0 (Real.pi / 2) :=
    Real.contDiff_cos.contDiffOn.absolutelyContinuousOnInterval
  have hBac :
      AbsolutelyContinuousOnInterval (fun t => (firstTangentPoint f fD t).1) 0 (Real.pi / 2) ∧
        AbsolutelyContinuousOnInterval (fun t => (firstTangentPoint f fD t).2) 0 (Real.pi / 2) :=
    absolutelyContinuousOnInterval_supportPoint (hfAC.sub hconst) hfDAC
  have hDac :
      AbsolutelyContinuousOnInterval (fun t => (secondTangentPoint g gD t).1) 0 (Real.pi / 2) ∧
        AbsolutelyContinuousOnInterval (fun t => (secondTangentPoint g gD t).2) 0 (Real.pi / 2) :=
    absolutelyContinuousOnInterval_companionSupportPoint (hgAC.sub hconst) hgDAC
  have hCXac : AbsolutelyContinuousOnInterval (fun t => (innerCornerPoint f g t).1)
      0 (Real.pi / 2) :=
    ((hfAC.sub hconst).mul hcos).sub ((hgAC.sub hconst).mul hsin)
  have hCYac : AbsolutelyContinuousOnInterval (fun t => (innerCornerPoint f g t).2)
      0 (Real.pi / 2) :=
    ((hfAC.sub hconst).mul hsin).add ((hgAC.sub hconst).mul hcos)
  have hp : Continuous (supportP fD g) := (hfD.sub hg).add continuous_const
  have hq : Continuous (supportQ gD f) := (hgD.add hf).sub continuous_const
  have hc : Continuous (cornerDensity f g fD gD) := by
    unfold cornerDensity supportP supportQ; fun_prop
  have hCX : Continuous (innerCornerDX f g fD gD) := by
    unfold innerCornerDX supportP supportQ; fun_prop
  have hCY : Continuous (innerCornerDY f g fD gD) := by
    unfold innerCornerDY supportP supportQ; fun_prop
  have hfDD' := hfDD.mono_set hsubB
  have hgDD' := hgDD.mono_set hsubD
  have hBrho : IntervalIntegrable (fun t => f t - 1 + fDD t) volume b (Real.pi / 2) :=
    ((hf.sub continuous_const).intervalIntegrable _ _).add hfDD'
  have hDrho : IntervalIntegrable (fun t => g t - 1 + gDD t) volume 0 d :=
    ((hg.sub continuous_const).intervalIntegrable _ _).add hgDD'

  have hDi := twice_integral_graph_parametrization_ac h0d (hDac.1.mono hsubD) (hDac.2.mono hsubD)
    (XD := companionSupportPointDX (fun s => g s - 1) gDD)
    (YD := companionSupportPointDY (fun s => g s - 1) gDD)
    (hderivD.mono fun t ht => hasDerivAt_companionSupportPoint_fst (ht.2.1.sub_const 1) ht.2.2.2)
    (hderivD.mono fun t ht => hasDerivAt_companionSupportPoint_snd (ht.2.1.sub_const 1) ht.2.2.2)
    (hDrho.neg.mul_continuousOn Real.continuous_cos.continuousOn)
    (hDrho.neg.mul_continuousOn Real.continuous_sin.continuousOn) hN.continuousOn hgraphD
  have hCi := twice_integral_graph_parametrization_ac hbd (hCXac.mono hsubC) (hCYac.mono hsubC)
    (XD := innerCornerDX f g fD gD) (YD := innerCornerDY f g fD gD)
    (hderivC.mono fun t ht => (((ht.1.sub_const 1).mul (Real.hasDerivAt_cos t)).sub
      ((ht.2.1.sub_const 1).mul (Real.hasDerivAt_sin t))).congr_deriv
      (by simp only [innerCornerDX, supportP, supportQ]; ring))
    (hderivC.mono fun t ht => (((ht.1.sub_const 1).mul (Real.hasDerivAt_sin t)).add
      ((ht.2.1.sub_const 1).mul (Real.hasDerivAt_cos t))).congr_deriv
      (by simp only [innerCornerDY, supportP, supportQ]; ring))
    (hCX.intervalIntegrable _ _) (hCY.intervalIntegrable _ _) hN.continuousOn hgraphC
  have hBi := twice_integral_graph_parametrization_ac hbL (hBac.1.mono hsubB) (hBac.2.mono hsubB)
    (XD := supportPointDX (fun s => f s - 1) fDD) (YD := supportPointDY (fun s => f s - 1) fDD)
    (hderivB.mono fun t ht => hasDerivAt_supportPoint_fst (ht.1.sub_const 1) ht.2.2.1)
    (hderivB.mono fun t ht => hasDerivAt_supportPoint_snd (ht.1.sub_const 1) ht.2.2.1)
    (hBrho.neg.mul_continuousOn Real.continuous_sin.continuousOn)
    (hBrho.mul_continuousOn Real.continuous_cos.continuousOn) hN.continuousOn hgraphB
  rw [← innerCorner_eq_secondTangent_of_momentum_zero hqzero] at hDi
  rw [← innerCorner_eq_firstTangent_of_momentum_zero hpzero] at hBi
  simp only [Prod.mk.eta, secondTangentPoint, firstTangentPoint, coordDet_companionSupportPoint,
    coordDet_supportPoint, coordDet_innerCorner] at hDi hCi hBi
  simp only [companionSupportPoint_coordinates, Reference.supportPoint, hFtop, hGtop,
    Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two, sub_self, mul_zero,
    mul_one, zero_sub, sub_zero, add_zero] at hDi hBi
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hN.intervalIntegrable (μ := volume) (-gD 0) (innerCornerPoint f g b).1)
    (hN.intervalIntegrable (innerCornerPoint f g b).1 (innerCornerPoint f g d).1)
  have hjoin := intervalIntegral.integral_add_adjacent_intervals
    (hN.intervalIntegrable (μ := volume) (-gD 0) (innerCornerPoint f g b).1)
    (hN.intervalIntegrable (innerCornerPoint f g b).1 (-fD (Real.pi / 2)))
  have hB := integral_density_of_identity (firstTangent_density_identity f g fD gD fDD) hc hp
    (((hfD.mul hp).intervalIntegrable _ _).add
      ((hfDD'.sub (hgD.intervalIntegrable _ _)).continuousOn_mul
        (hf.sub continuous_const).continuousOn))
    (integral_eq_sub_of_ac_of_ae_hasDerivAt hbL (E := firstMomentumPrimitive f g fD)
      (((hfAC.sub hconst).mul ((hfDAC.sub hgAC).add hconst)).mono hsubB)
      (hderivB.mono fun t ht => (ht.1.sub_const 1).mul ((ht.2.2.1.sub ht.2.1).add_const 1)))
  have hD := integral_density_of_identity (secondTangent_density_identity f g fD gD gDD) hc hq
    (((hgD.mul hq).intervalIntegrable _ _).add
      ((hgDD'.add (hfD.intervalIntegrable _ _)).continuousOn_mul
        (hg.sub continuous_const).continuousOn))
    (integral_eq_sub_of_ac_of_ae_hasDerivAt h0d (E := secondMomentumPrimitive f g gD)
      (((hgAC.sub hconst).mul ((hgDAC.add hfAC).sub hconst)).mono hsubD)
      (hderivD.mono fun t ht => (ht.2.1.sub_const 1).mul ((ht.2.2.2.add ht.1).sub_const 1)))
  simp only [firstMomentumPrimitive, secondMomentumPrimitive, hFtop, hGtop, hpzero, hqzero,
    sub_self, zero_mul, mul_zero, add_zero] at hB hD
  have hsplit0 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 d) (hc.intervalIntegrable d (Real.pi / 2))
  have hsplitb := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) b d) (hc.intervalIntegrable d (Real.pi / 2))
  linarith

theorem sweptNiche_integral_eq_signed_formula
    {U : Set Plane} (hU : IsCompact U) {b d : ℝ}
    {f g fD gD fDD gDD : ℝ → ℝ}
    (hb0 : 0 ≤ b) (hbd : b ≤ d) (hdL : d ≤ Real.pi / 2)
    (hN : Continuous (sweptNiche U (Real.pi / 2)))
    (hf : Continuous f) (hg : Continuous g) (hfD : Continuous fD) (hgD : Continuous gD)
    (hderivF : ∀ t, HasDerivWithinAt f (fD t) (Ioi t) t)
    (hderivG : ∀ t, HasDerivWithinAt g (gD t) (Ioi t) t)
    (hsecondF : ∀ t, HasDerivWithinAt fD (fDD t) (Ioi t) t)
    (hsecondG : ∀ t, HasDerivWithinAt gD (gDD t) (Ioi t) t)
    (hfDD : IntervalIntegrable fDD volume 0 (Real.pi / 2))
    (hgDD : IntervalIntegrable gDD volume 0 (Real.pi / 2))
    (hFsupport : ∀ t ∈ Icc 0 (Real.pi / 2), support U (unitNormal t) = f t)
    (hGsupport : ∀ t ∈ Icc 0 (Real.pi / 2), support U (companionNormal t) = g t)
    (hFtop : f (Real.pi / 2) = 1) (hGtop : g 0 = 1)
    (hFcurv : ∀ t ∈ Icc 0 (Real.pi / 2), f t + fDD t ≤ 1)
    (hGcurv : ∀ t ∈ Icc 0 (Real.pi / 2), g t + gDD t ≤ 1)
    (hpzero : supportP fD g b = 0) (hqzero : supportQ gD f d = 0)
    (hp : ∀ t ∈ Icc b (Real.pi / 2), supportP fD g t ≤ 0)
    (hq : ∀ t ∈ Icc 0 d, 0 ≤ supportQ gD f t) :
    2 * (∫ x in (-gD 0)..(-fD (Real.pi / 2)), sweptNiche U (Real.pi / 2) x) =
      -(∫ t in (0 : ℝ)..(Real.pi / 2), cornerDensity f g fD gD t) +
      (∫ t in b..(Real.pi / 2), supportP fD g t ^ 2) +
      ∫ t in (0 : ℝ)..d, supportQ gD f t ^ 2 := by
  have hfAC := absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi hf hderivF
    (hfD.intervalIntegrable 0 (Real.pi / 2))
  have hgAC := absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi hg hderivG
    (hgD.intervalIntegrable 0 (Real.pi / 2))
  have hfDAC := absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi hfD hsecondF hfDD
  have hgDAC := absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi hgD hsecondG hgDD
  have hB : ∀ t ∈ Ioo 0 (Real.pi / 2), ∀ s ∈ Icc 0 (Real.pi / 2),
      f s - 1 ≤ coordDot (firstTangentPoint f fD t) (unitNormal s) := fun t ht s hs =>
    firstTangent_dominates_support hf hfD hderivF hsecondF hFcurv (Ioo_subset_Icc_self ht) hs
  have hD : ∀ t ∈ Ioo 0 (Real.pi / 2), ∀ s ∈ Icc 0 (Real.pi / 2),
      g s - 1 ≤ coordDot (secondTangentPoint g gD t) (companionNormal s) := fun t ht s hs =>
    secondTangent_dominates_support hg hgD hderivG hsecondG hGcurv (Ioo_subset_Icc_self ht) hs
  refine signedRoof_integral_of_graphs_ac hb0 hbd hdL hN hf hg hfD hgD hfAC hgAC hfDAC hgDAC
    (by filter_upwards [ae_hasDerivAt_of_hasDerivWithinAt_Ioi hfAC hderivF,
          ae_hasDerivAt_of_hasDerivWithinAt_Ioi hgAC hderivG,
          ae_hasDerivAt_of_hasDerivWithinAt_Ioi hfDAC hsecondF,
          ae_hasDerivAt_of_hasDerivWithinAt_Ioi hgDAC hsecondG] with t h1 h2 h3 h4
        using ⟨h1, h2, h3, h4⟩)
    hfDD hgDD hFtop hGtop hpzero hqzero (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨ht.1, ht.2.trans_le hdL⟩
    exact sweptNiche_secondTangent hU hFsupport hGsupport hGtop htL (hq t ⟨ht.1.le, ht.2.le⟩)
      (hD t htL)
  · have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨hb0.trans_lt ht.1, ht.2.trans_le hdL⟩
    exact sweptNiche_innerCorner hU hFsupport hGsupport hFtop htL (hp t ⟨ht.1.le, htL.2.le⟩)
      (hq t ⟨htL.1.le, ht.2.le⟩) (hB t htL) (hD t htL)
  · have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨hb0.trans_lt ht.1, ht.2⟩
    exact sweptNiche_firstTangent hU hFsupport hGsupport hFtop htL (hp t ⟨ht.1.le, ht.2.le⟩)
      (hB t htL)

end AmbidextrousSofa

end BPn42

end BP42

section BP43

noncomputable section BPn43

open Set MeasureTheory

namespace AmbidextrousSofa

def symmetricTrim (K : Set Plane) (N : ℝ → ℝ) : Set Plane :=
  {p | p ∈ K ∧ N p.1 ≤ p.2 ∧ N p.1 ≤ 1 - p.2}

theorem volumeReal_symmetricTrim_eq_cap_area {K : Set Plane} (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) (hstrip : K ⊆ unitStrip)
    (hreflect : ∀ p ∈ K, reflect p ∈ K) {N : ℝ → ℝ}
    (hN : Continuous N) (hNnonneg : ∀ x ∈ horizontalProjection K, 0 ≤ N x)
    (hNhalf : ∀ x ∈ horizontalProjection K, N x ≤ 1 / 2)
    (hseparate : ∀ x ∈ horizontalProjection K, capRoof (upperCap K) x = 1 ∨ N x = 0) :
    volume.real (symmetricTrim K N) = 2 * volume.real (upperCap K) -
      capWidth (upperCap K) - 2 * ∫ x in horizontalProjection K, N x := by
  have hcap := isDownwardCap_upperCap hne hK hconv hstrip
  have hK0 : ∀ p ∈ K, 0 ≤ p.2 := fun p hp => (hstrip hp).1
  have hroof := capRoof_upperCap hK hK0

  have htrim : symmetricTrim K N = fourWallEnvelope (horizontalProjection K)
      (roofDeficit (upperCap K)) (roofDeficit (upperCap K)) N N := by
    ext p
    simp only [symmetricTrim, fourWallEnvelope, fourWallFiber, roofDeficit, hroof, sub_sub_cancel]
    constructor
    · rintro ⟨hp, hlo, hhi⟩
      have h : 1 - p.2 ≤ capRoof K p.1 := le_capRoof hK (hreflect p hp)
      exact ⟨mem_image_of_mem Prod.fst hp, by linarith, hlo, le_capRoof hK hp, by linarith⟩
    · rintro ⟨hx, hlo, hnlo, hhi, hnhi⟩
      have hl : (p.1, 1 - capRoof K p.1) ∈ K := hreflect _ (capRoof_mem hK hx)
      exact ⟨(convex_verticalFiber hconv p.1).ordConnected.out hl (capRoof_mem hK hx) ⟨hlo, hhi⟩,
        hnlo, by linarith⟩

  have hfiber : ∀ x ∈ horizontalProjection K, signedFiberLength (roofDeficit (upperCap K) x)
      (roofDeficit (upperCap K) x) (N x) (N x) = 2 * capRoof (upperCap K) x - 1 - 2 * N x := by
    intro x hx
    simp only [signedFiberLength, roofDeficit]
    rcases hseparate x hx with h | h
    · rw [h, sub_self, max_eq_right (hNnonneg x hx)]; ring
    · rw [h, max_eq_left (sub_nonneg.2 (capRoof_le_one hcap.isCompact hcap.inStrip x))]; ring
  have hprojection := isCompact_horizontalProjection hK
  have hI := hprojection.measurableSet
  have hfinite : volume (horizontalProjection K) ≠ ⊤ := hprojection.measure_ne_top
  have hP : horizontalProjection K =
      Icc (horizontalLeft (upperCap K)) (horizontalRight (upperCap K)) := by
    rw [← horizontalProjection_upperCap hK0,
      hcap.horizontalProjection_eq_Icc]
  have hroofI : IntegrableOn (capRoof (upperCap K)) (horizontalProjection K) :=
    hP ▸ hcap.integrableOn_capRoof_Icc _ _
  have hdI : IntegrableOn (roofDeficit (upperCap K)) (horizontalProjection K) :=
    hP ▸ hcap.integrableOn_roofDeficit_Icc _ _
  have hNI : IntegrableOn N (horizontalProjection K) :=
    hN.continuousOn.integrableOn_compact hprojection
  have hvol := volumeReal_fourWallEnvelope_eq_signedIntegral hI hcap.measurable_roofDeficit
    hcap.measurable_roofDeficit hN.measurable hN.measurable
    (integrableOn_signedFiberLength hfinite hdI hdI hNI hNI) <| by
      filter_upwards [ae_restrict_mem hI] with x hx
      have h : 1 - capRoof K x ≤ capRoof K x := le_capRoof hK (hreflect _ (capRoof_mem hK hx))
      rw [hfiber x hx, hroof]
      rcases hseparate x hx with h' | h' <;> linarith [hroof x, hNhalf x hx]
  have hOne := integrableOn_const (μ := volume) (C := (1 : ℝ)) hfinite
  have h2 := hroofI.const_mul 2
  rw [← htrim, setIntegral_congr_fun hI hfiber, integral_sub (IntegrableOn.fun_sub h2 hOne)
    (hNI.const_mul 2), integral_sub h2 hOne, integral_const_mul, integral_const_mul,
    setIntegral_const, smul_eq_mul, mul_one] at hvol
  have hwidth : volume.real (horizontalProjection K) = capWidth (upperCap K) := by
    rw [hP, Real.volume_real_Icc_of_le
      (horizontalLeft_le_horizontalRight hcap.nonempty hcap.isCompact)]
    rfl
  rw [hvol, hwidth, hcap.volumeReal_eq_integral_capRoof, ← hP]

end AmbidextrousSofa

end BPn43

end BP43

section BP44

noncomputable section BPn44

open Set MeasureTheory
open AmbidextrousSofa.Analysis

namespace AmbidextrousSofa.Reference

theorem twice_density_sub_self_variation (u : QuarterPair) (t : ℝ) :
    2 * adaptiveDensity u t - adaptiveLinearDensity u u t =
      2 - u.f t - u.g t + (u.fD t - u.gD t) / 2 - min (u.p t) 0 + max (u.q t) 0 := by
  simp only [adaptiveDensity, adaptiveLinearDensity, min_def, max_def, QuarterPair.p,
    QuarterPair.q]
  split_ifs <;> ring

def referenceValueRemainder (t : ℝ) : ℝ :=
  2 - referenceF t - referenceG t + (referenceFD t - referenceGD t) / 2 -
    min (momentP t) 0 + max (momentQ t) 0

theorem integral_referenceValueRemainder :
    (∫ t in (0 : ℝ)..(Real.pi / 2), referenceValueRemainder t) =
      4 * A * cosBeta - 8 / 3 * A - 1 + beta := by
  have hi (a b : ℝ) : IntervalIntegrable referenceValueRemainder volume a b := by
    unfold referenceValueRemainder momentP momentQ
    exact Continuous.intervalIntegrable (by (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop)) a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 lateSwitch) (hi _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (hi 0 beta) (hi _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le beta_pos.le (f := fun t =>
      t / 2 + (2 * A - 1 / 4) * Real.cos t + (A - 3 / 4) * Real.sin t) (by (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop)) ?_ (hi _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le beta_lt_lateSwitch.le
      (f := fun t => (referenceG t - referenceF t) / 2) (by (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop)) ?_ (hi _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le lateSwitch_lt_pi_div_two.le (f := fun t =>
      t / 2 - (1 / 4 - A / 3) * Real.cos t - (3 / 4 + 2 / 3 * A) * Real.sin t) (by (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop)) ?_
      (hi _ _)]
  · simp only [referenceF, referenceG, le_refl, ite_true, not_le.mpr beta_lt_lateSwitch, ite_false,
      f_matching_last, g_matching_last]
    simp only [fEarly, gEarly, fLate, gLate, lateSwitch, Real.sin_zero, Real.cos_zero,
      Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
      cosBeta]
    ring
  · intro t ht
    rw [referenceValueRemainder,
      min_eq_left (momentP_nonpos_after_beta ⟨beta_lt_lateSwitch.le.trans ht.1.le, ht.2.le⟩),
      max_eq_right (momentQ_nonpos_late ⟨ht.1.le, ht.2.le⟩)]
    simp only [momentP, referenceF, referenceG, referenceFD, referenceGD,
      not_le.mpr (beta_lt_lateSwitch.trans ht.1), not_le.mpr ht.1, ite_false, fLate, gLate, fLateD,
      gLateD]
    exact ((((hasDerivAt_id t).div_const 2).sub ((Real.hasDerivAt_cos t).const_mul _)).sub
      ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by ring)
  · intro t ht
    rw [referenceValueRemainder,
      min_eq_left (momentP_nonpos_after_beta ⟨ht.1.le, ht.2.le.trans lateSwitch_lt_pi_div_two.le⟩),
      max_eq_left (momentQ_nonneg_before_lateSwitch ⟨beta_pos.le.trans ht.1.le, ht.2.le⟩)]
    exact (((hasDerivAt_referenceG t).sub (hasDerivAt_referenceF t)).div_const 2).congr_deriv
      (by unfold momentP momentQ; ring)
  · intro t ht
    rw [referenceValueRemainder, min_eq_right (momentP_nonneg_early ⟨ht.1.le, ht.2.le⟩),
      max_eq_left (momentQ_nonneg_before_lateSwitch ⟨ht.1.le, ht.2.le.trans beta_lt_lateSwitch.le⟩)]
    simp only [momentQ, referenceF, referenceG, referenceFD, referenceGD, ht.2.le, ite_true,
      fEarly, gEarly, fEarlyD, gEarlyD]
    exact ((((hasDerivAt_id t).div_const 2).add ((Real.hasDerivAt_cos t).const_mul _)).add
      ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by ring)

theorem reference_self_variation :
    adaptiveFirstVariation referencePair referencePair = 16 / 3 * A - 1 := by
  rw [adaptiveFirstVariation_eq_boundary referencePair referencePair
    (fun _ => referencePair_eulerF) (fun _ => referencePair_eulerG)]
  simp only [QuarterPair.fluxF, QuarterPair.fluxG]
  rw [min_eq_left (show referencePair.p (Real.pi / 2) ≤ 0 from
      momentP_nonpos_after_beta ⟨beta_lt_pi_div_two.le, le_rfl⟩),
    min_eq_right (show 0 ≤ referencePair.p 0 from momentP_nonneg_early ⟨le_rfl, beta_pos.le⟩),
    max_eq_right (show referencePair.q (Real.pi / 2) ≤ 0 from
      momentQ_nonpos_late ⟨lateSwitch_lt_pi_div_two.le, le_rfl⟩),
    max_eq_left (show 0 ≤ referencePair.q 0 from
      momentQ_nonneg_before_lateSwitch ⟨le_rfl, lateSwitch_pos.le⟩)]
  simp only [QuarterPair.p, QuarterPair.q, referencePair, referenceF_zero, referenceG_zero,
    referenceF_pi_div_two, referenceG_pi_div_two, referenceFD_zero, referenceGD_zero,
    referenceFD_pi_div_two, referenceGD_pi_div_two]
  ring

theorem adaptiveFunctional_reference_eq_M_add_width :
    adaptiveFunctional referencePair = (M + 8 / 3 * A) / 2 := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h : ∫ t in (0 : ℝ)..(Real.pi / 2), (2 * adaptiveDensity referencePair t -
      adaptiveLinearDensity referencePair referencePair t) =
      4 * A * cosBeta - 8 / 3 * A - 1 + beta :=
    (intervalIntegral.integral_congr fun t _ =>
      twice_density_sub_self_variation referencePair t).trans integral_referenceValueRemainder
  rw [intervalIntegral.integral_sub
    (((continuousOn_adaptiveDensity referencePair).intervalIntegrable_of_Icc hL).const_mul 2)
    ((continuousOn_adaptiveLinearDensity referencePair referencePair).intervalIntegrable_of_Icc hL),
    intervalIntegral.integral_const_mul, ← adaptiveFunctional, ← adaptiveFirstVariation,
    reference_self_variation] at h
  have hY : 4 * A * cosBeta = M - beta + 2 := by
    rw [mul_assoc, A_mul_cosBeta, eq_div_of_mul_eq Y_ne_zero M_sub_beta_add_two_mul_Y]
    ring
  linarith

theorem intervalIntegrable_if_lt {a b c : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t => if t < c then f t else g t) volume a b := by
  rw [intervalIntegrable_iff] at hf hg ⊢
  exact Integrable.piecewise (s := Iio c) measurableSet_Iio hf.integrableOn hg.integrableOn

theorem neg_referenceGD_zero : -referenceGD 0 = topLeft := by
  rw [referenceGD_zero, topLeft]; ring

theorem neg_referenceFD_pi_div_two : -referenceFD (Real.pi / 2) = topRight := by
  rw [referenceFD_pi_div_two, topRight]; ring

theorem adaptiveFunctional_reference_eq_cap_area_sub_niche :
    adaptiveFunctional referencePair = volume.real referenceCap -
      ∫ x in topLeft..topRight, referenceNiche x := by
  have hF := continuous_referenceF; have hG := continuous_referenceG
  have hFD := continuous_referenceFD; have hGD := continuous_referenceGD
  have hI {f : ℝ → ℝ} (hf : Continuous f) : IntervalIntegrable f volume 0 (Real.pi / 2) :=
    hf.intervalIntegrable _ _
  have hFs : IntervalIntegrable referenceFSecond volume 0 (Real.pi / 2) :=
    intervalIntegrable_if_lt (hI (by (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop))) (intervalIntegrable_if_lt (hI (by (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop)))
      (hI (by (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop))))
  have hGs : IntervalIntegrable referenceGSecond volume 0 (Real.pi / 2) :=
    intervalIntegrable_if_lt (hI (by (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop))) (intervalIntegrable_if_lt (hI (by (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop)))
      (hI (by (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop))))
  have hFDac := absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi hFD
    hasDerivWithinAt_referenceFD_right hFs
  have hGDac := absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi hGD
    hasDerivWithinAt_referenceGD_right hGs
  have harea := isDownwardCap_referenceCap.volumeReal_eq_support_energy_ac
    (absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi hF
      (fun t => (hasDerivAt_referenceF t).hasDerivWithinAt) (hI hFD))
    (absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi hG
      (fun t => (hasDerivAt_referenceG t).hasDerivWithinAt) (hI hGD)) hFDac hGDac
    (.of_forall hasDerivAt_referenceF) (.of_forall hasDerivAt_referenceG)
    (ae_hasDerivAt_of_hasDerivWithinAt_Ioi hFDac hasDerivWithinAt_referenceFD_right)
    (ae_hasDerivAt_of_hasDerivWithinAt_Ioi hGDac hasDerivWithinAt_referenceGD_right) hFs hGs
    (fun _ ht => referenceHull_subset_referenceCap (fBoundary_mem_referenceHull ht))
    (fun _ ht => referenceHull_subset_referenceCap (gBoundary_mem_referenceHull ht))
    (fun _ ht => angleSupport_referenceCap_eq_f ⟨ht.1.le, ht.2.le⟩)
    (fun _ ht => angleSupport_referenceCap_eq_g ⟨ht.1.le, ht.2.le⟩)
    (by rw [horizontalLeft_referenceCap, referenceG_pi_div_two]; ring)
    (by rw [horizontalRight_referenceCap, referenceF_zero]) referenceF_pi_div_two referenceG_zero
    (by rw [neg_referenceGD_zero, neg_referenceFD_pi_div_two]; exact topLeft_lt_topRight.le)
    (fun x hx => capRoof_referenceCap_eq_one
      (by rwa [neg_referenceGD_zero, neg_referenceFD_pi_div_two] at hx))
  have hniche := sweptNiche_integral_eq_signed_formula isCompact_referenceHull
    beta_pos.le beta_lt_lateSwitch.le lateSwitch_lt_pi_div_two.le continuous_referenceNiche
    hF hG hFD hGD (fun t => (hasDerivAt_referenceF t).hasDerivWithinAt)
    (fun t => (hasDerivAt_referenceG t).hasDerivWithinAt)
    hasDerivWithinAt_referenceFD_right hasDerivWithinAt_referenceGD_right hFs hGs
    (fun _ => angleSupport_referenceHull_eq_f)
    (fun t ht => companionNormal_eq_unitNormal t ▸ angleSupport_referenceHull_eq_g ht)
    referenceF_pi_div_two referenceG_zero
    (fun t _ => (referenceF_right_curvature t).2.le)
    (fun t _ => referenceG_right_curvature_le_one t)
    momentP_beta momentQ_lateSwitch (fun _ => momentP_nonpos_after_beta)
    (fun _ => momentQ_nonneg_before_lateSwitch)
  rw [neg_referenceGD_zero, neg_referenceFD_pi_div_two] at hniche
  have hP : Continuous (supportP referenceFD referenceG) := by unfold supportP; (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop)
  have hQ : Continuous (supportQ referenceGD referenceF) := by unfold supportQ; (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop)
  have hC : Continuous (cornerDensity referenceF referenceG referenceFD referenceGD) := by
    unfold cornerDensity; (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop)
  have hsplit : 2 * adaptiveFunctional referencePair = ∫ t in (0 : ℝ)..(Real.pi / 2),
      ((referenceF t ^ 2 - referenceFD t ^ 2) + (referenceG t ^ 2 - referenceGD t ^ 2) +
        cornerDensity referenceF referenceG referenceFD referenceGD t -
        min (supportP referenceFD referenceG t) 0 ^ 2) -
        max (supportQ referenceGD referenceF t) 0 ^ 2 := by
    rw [adaptiveFunctional, ← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    simp only [adaptiveDensity, referencePair, QuarterPair.p, QuarterPair.q, cornerDensity,
      supportP, supportQ]
    ring
  rw [intervalIntegral.integral_sub (hI ?_) (hI ?_), intervalIntegral.integral_sub (hI ?_) (hI ?_),
    intervalIntegral.integral_add (hI ?_) (hI ?_),
    integral_min_sq_of_sign_switch beta_pos.le beta_lt_pi_div_two.le hP
      (fun _ => momentP_nonneg_early) (fun _ => momentP_nonpos_after_beta),
    integral_max_sq_of_sign_switch lateSwitch_pos.le lateSwitch_lt_pi_div_two.le hQ
      (fun _ => momentQ_nonneg_before_lateSwitch) (fun _ => momentQ_nonpos_late)] at hsplit
  · unfold referenceNiche
    linarith
  all_goals (have _c0 := continuous_referenceF; have _c1 := continuous_referenceG; have _c2 := continuous_referenceFD; have _c3 := continuous_referenceGD; fun_prop)

theorem integral_topInterval_referenceNiche :
    (∫ x in topInterval, referenceNiche x) =
      ∫ x in topLeft..topRight, referenceNiche x := by
  rw [topInterval, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le topLeft_lt_topRight.le]

theorem volumeReal_referenceSofa : volume.real referenceSofa = M := by
  have harea := volumeReal_symmetricTrim_eq_cap_area referenceHull_nonempty
    isCompact_referenceHull convex_referenceHull referenceHull_subset_unitStrip
    (fun p hp => (reflect_mem_referenceHull p).mpr hp) continuous_referenceNiche
    (fun x _ => referenceNiche_nonneg x) (fun x _ => (referenceNiche_lt_half x).le)
    fun x _ => (em (x ∈ topInterval)).imp capRoof_referenceCap_eq_one
      referenceNiche_eq_zero_outside
  change volume.real referenceSofa = 2 * volume.real referenceCap -
    capWidth referenceCap - 2 * ∫ x in horizontalProjection referenceHull, referenceNiche x at harea
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (isCompact_horizontalProjection isCompact_referenceHull).measurableSet
    (fun x hx => ⟨(x, 1), topFace_mem_referenceHull hx, rfl⟩)
    (fun x hx => referenceNiche_eq_zero_outside hx.2), integral_topInterval_referenceNiche,
    capWidth_referenceCap] at harea
  linarith [adaptiveFunctional_reference_eq_cap_area_sub_niche,
    adaptiveFunctional_reference_eq_M_add_width]

end AmbidextrousSofa.Reference

end BPn44

end BP44

section BP45

noncomputable section BPn45

open Set

namespace AmbidextrousSofa

theorem rotate_rotate (θ φ : ℝ) (p : Plane) : rotate θ (rotate φ p) = rotate (θ + φ) p := by
  apply Prod.ext <;> simp only [rotate, Real.cos_add, Real.sin_add] <;> ring

theorem rotate_add_vector (θ : ℝ) (p q : Plane) :
    rotate θ (p + q) = rotate θ p + rotate θ q := by
  apply Prod.ext <;> simp only [rotate, Prod.fst_add, Prod.snd_add] <;> ring

end AmbidextrousSofa

end BPn45

end BP45
noncomputable section

open Set Real MeasureTheory
open scoped ENNReal unitInterval EuclideanGeometry

namespace AmbidextrousSofa.FCBridge

abbrev Point := EuclideanSpace ℝ (Fin 2)

abbrev Motion := Point ≃ᵃⁱ[ℝ] Point

def coordinates (p : Point) : Plane := (p 0, p 1)

def point (p : Plane) : Point := !₂[p.1, p.2]

theorem coordinates_point (p : Plane) : coordinates (point p) = p := rfl

theorem point_coordinates (p : Point) : point (coordinates p) = p := by
  ext i
  fin_cases i <;> rfl

theorem coordinates_injective : Function.Injective coordinates :=
  Function.LeftInverse.injective point_coordinates

theorem point_continuous : Continuous point := by
  unfold point
  fun_prop

theorem coordinates_add (p q : Point) :
    coordinates (p + q) = coordinates p + coordinates q := rfl

def coordinatesMeasurableEquiv : Point ≃ᵐ Plane :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem coordinates_measurePreserving :
    MeasurePreserving coordinates (volume : Measure Point) volume :=
  (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

theorem coordinates_point_image (s : Set Plane) : coordinates '' (point '' s) = s := by
  rw [image_image]
  simp only [coordinates_point, image_id']

theorem volume_coordinates_image (s : Set Point) : volume (coordinates '' s) = volume s := by
  have h := coordinates_measurePreserving.measure_preimage_emb
    coordinatesMeasurableEquiv.measurableEmbedding (coordinates '' s)
  rw [preimage_image_eq s coordinates_injective] at h
  exact h.symm

theorem volume_point_image (s : Set Plane) : volume (point '' s) = volume s := by
  rw [← volume_coordinates_image, coordinates_point_image]

theorem mem_horizontalHallway_iff (p : Point) :
    p ∈ MovingSofa.horizontalHallway ↔ coordinates p ∈ incomingArm := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy
  · intro hp
    exact ⟨p 0, p 1, hp, by ext i; fin_cases i <;> rfl⟩

theorem mem_verticalHallway_iff (p : Point) :
    p ∈ MovingSofa.verticalHallway ↔ coordinates p ∈ lowerOutgoingArm := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy
  · intro hp
    exact ⟨p 0, p 1, hp, by ext i; fin_cases i <;> rfl⟩

theorem mem_hallway_iff (p : Point) : p ∈ MovingSofa.hallway ↔ coordinates p ∈ lowerHall := by
  simp only [MovingSofa.hallway, lowerHall, mem_union, mem_horizontalHallway_iff,
    mem_verticalHallway_iff]

theorem reflection_midline_apply (q : Point) :
    EuclideanGeometry.reflection MovingSofa.midline q = !₂[q 0, 1 - q 1] := by
  rw [EuclideanGeometry.reflection_apply_of_mem MovingSofa.midline q
      (AffineSubspace.self_mem_mk' _ _),
    MovingSofa.midline, AffineSubspace.direction_mk', Submodule.reflection_apply,
    Submodule.starProjection_singleton]
  ext i
  fin_cases i <;> simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.vecHead] <;> ring

theorem coordinates_image_reflection (s : Set Point) :
    coordinates '' (EuclideanGeometry.reflection MovingSofa.midline '' s) =
      reflect '' (coordinates '' s) := by
  rw [image_image, image_image]
  congr 1
  funext p
  rw [reflection_midline_apply]
  rfl

theorem reflection_image_point (S : Set Plane) :
    EuclideanGeometry.reflection MovingSofa.midline '' (point '' S) = point '' (reflect '' S) := by
  apply Set.image_injective.2 coordinates_injective
  rw [coordinates_image_reflection, coordinates_point_image, coordinates_point_image]

theorem norm_sq_coordinates (p : Point) : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

def euclideanRotate (t : ℝ) (p : Point) : Point :=
  !₂[cos t * p 0 - sin t * p 1, sin t * p 0 + cos t * p 1]

theorem euclideanRotate_coordinates (t : ℝ) (p : Point) :
    coordinates (euclideanRotate t p) = rotate t (coordinates p) := rfl

theorem euclideanRotate_norm (t : ℝ) (p : Point) : ‖euclideanRotate t p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_coordinates, norm_sq_coordinates]
  change (cos t * p 0 - sin t * p 1) ^ 2 + (sin t * p 0 + cos t * p 1) ^ 2 = (p 0) ^ 2 + (p 1) ^ 2
  linear_combination ((p 0) ^ 2 + (p 1) ^ 2) * sin_sq_add_cos_sq t

def rotationLinearEquiv (t : ℝ) : Point ≃ₗ[ℝ] Point where
  toFun := euclideanRotate t
  invFun := euclideanRotate (-t)
  left_inv p := by
    apply coordinates_injective
    simp only [euclideanRotate_coordinates, rotate_rotate, neg_add_cancel, rotate_zero]
  right_inv p := by
    apply coordinates_injective
    simp only [euclideanRotate_coordinates, rotate_rotate, add_neg_cancel, rotate_zero]
  map_add' p q := by
    apply coordinates_injective
    simp only [euclideanRotate_coordinates, coordinates_add, rotate_add_vector]
  map_smul' a p := by
    apply coordinates_injective
    simp only [euclideanRotate_coordinates, RingHom.id_apply]
    apply Prod.ext <;> simp [coordinates, rotate, euclideanRotate] <;> ring

def rotation (t : ℝ) : Point ≃ₗᵢ[ℝ] Point :=
  { rotationLinearEquiv t with norm_map' := euclideanRotate_norm t }

def realization (ac : ℝ × Plane) : Motion :=
  (rotation ac.1).toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ (point ac.2))

theorem realization_coordinates (ac : ℝ × Plane) (p : Point) :
    coordinates (realization ac p) = rigidMap ac.1 ac.2 (coordinates p) := by
  change coordinates (euclideanRotate ac.1 p + point ac.2) = _
  rw [coordinates_add, euclideanRotate_coordinates, coordinates_point]
  rfl

def quarterTurn : Point →L[ℝ] Point where
  toFun p := !₂[-p 1, p 0]
  map_add' p q := by
    ext i
    fin_cases i <;> simp
    ring
  map_smul' a p := by
    ext i
    fin_cases i <;> simp
  cont := by fun_prop

theorem realization_toContinuousAffineMap (ac : ℝ × Plane) :
    (realization ac).toAffineIsometry.toContinuousAffineMap =
      (ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ Point Point).symm
        (point ac.2, cos ac.1 • (ContinuousLinearMap.id ℝ Point) + sin ac.1 • quarterTurn) := by
  ext p : 1
  apply coordinates_injective
  change coordinates (realization ac p) = _
  rw [realization_coordinates]
  change rigidMap ac.1 ac.2 (coordinates p) =
    coordinates ((cos ac.1 • p + sin ac.1 • quarterTurn p) + point ac.2)
  ext <;> simp [rigidMap, rotate, coordinates, quarterTurn, point] <;> ring

theorem realization_continuous : Continuous realization := by
  apply continuous_induced_rng.mpr
  change Continuous (fun ac : ℝ × Plane => (realization ac).toAffineIsometry.toContinuousAffineMap)
  simp_rw [realization_toContinuousAffineMap]
  apply (ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ Point Point).symm.continuous.comp
  exact (point_continuous.comp continuous_snd).prodMk
    (((Real.continuous_cos.comp continuous_fst).smul continuous_const).add
      ((Real.continuous_sin.comp continuous_fst).smul continuous_const))

theorem isMovingSofa_point {S : Set Plane} (hS : IsCompact S) (hconn : IsConnected S)
    {path : RigidMotionPath} (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hid : ∀ p, path.placement 0 p = p) : ∃ m, MovingSofa.IsMovingSofa (point '' S) m := by
  let m : I → Motion := fun t => realization (path.angle t, path.shift t)
  have hm : Continuous m := realization_continuous.comp
    ((path.continuous_angle.comp_continuous continuous_subtype_val fun t => t.2).prodMk
      (path.continuous_shift.comp_continuous continuous_subtype_val fun t => t.2))
  have hformula (t : I) (p : Plane) : coordinates (m t (point p)) = path.placement t p := by
    rw [realization_coordinates, coordinates_point]
    rfl
  refine ⟨m, hconn.image _ point_continuous.continuousOn, (hS.image point_continuous).isClosed, hm,
    ?_, ?_, ?_, ?_⟩
  · apply AffineIsometryEquiv.ext
    intro q
    apply coordinates_injective
    rw [← point_coordinates q, hformula, Set.Icc.coe_zero, hid]
    rfl
  · rintro _ ⟨p, hp, rfl⟩
    exact (mem_horizontalHallway_iff _).2 (by
      rw [coordinates_point, ← hid p]; exact h.start (mem_image_of_mem _ hp))
  · rintro t _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact (mem_hallway_iff _).2 (by rw [hformula]; exact h.inside t t.2 (mem_image_of_mem _ hp))
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact (mem_verticalHallway_iff _).2 (by
      rw [hformula, Set.Icc.coe_one]; exact h.finish (mem_image_of_mem _ hp))

theorem isAmbidextrousSofa_referenceSofa :
    MovingSofa.IsAmbidextrousSofa (point '' Reference.referenceSofa) := by
  have h := isMovingSofa_point Reference.isCompact_referenceSofa
    Reference.isConnected_referenceSofa Reference.referenceSofa_lowerPassage
    Reference.lowerReferencePath_start
  refine ⟨h, ?_⟩
  rwa [reflection_image_point, Reference.image_reflect_referenceSofa]

theorem romiksSofa_Y_eq : MovingSofa.RomiksSofa.Y = Y :=
  MovingSofa.RomiksSofa.existsUnique_Y.unique MovingSofa.RomiksSofa.existsUnique_Y.exists.choose_spec
    (by linear_combination Y_equation)

theorem romiksSofa_X_eq : MovingSofa.RomiksSofa.X = 1 + 4 * Y ^ 2 :=
  MovingSofa.RomiksSofa.existsUnique_X.unique MovingSofa.RomiksSofa.existsUnique_X.exists.choose_spec
    (by linear_combination 4 * (4 * Y ^ 3 + 3 * Y + 1) * Y_equation)

theorem area_eq : MovingSofa.RomiksSofa.area = M := by
  rw [MovingSofa.RomiksSofa.area, romiksSofa_X_eq, romiksSofa_Y_eq]
  rfl

end AmbidextrousSofa.FCBridge

theorem OMA.solution : OMA.R_MovingSofa_ambidextrousSofaConstant_eq_romiksSofa_area_R1.H2 := by
  refine ⟨_, AmbidextrousSofa.FCBridge.isAmbidextrousSofa_referenceSofa, ?_⟩
  rw [MeasureTheory.measureReal_def, AmbidextrousSofa.FCBridge.volume_point_image,
    ← MeasureTheory.measureReal_def, AmbidextrousSofa.Reference.volumeReal_referenceSofa,
    ← AmbidextrousSofa.FCBridge.area_eq, MovingSofa.RomiksSofa.area,
    AmbidextrousSofa.FCBridge.romiksSofa_X_eq, AmbidextrousSofa.FCBridge.romiksSofa_Y_eq]
