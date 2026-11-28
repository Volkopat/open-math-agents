import OMAStatements.S_mo_421887

/-!
River Li's answer (https://mathoverflow.net/a/425296) uses multiple-angle
formulas and the product of a number with its complement. Here those two
reductions lead to a rational interval estimate, checked by bisection.
-/

namespace OMA.S_mo_421887

/-- Upper bound for p(1-p) when 0 ≤ p ≤ v. -/
private def bump (v : ℚ) : ℚ := min v (1/2) * (1-min v (1/2))

private lemma bump_bound (p : ℝ) (v : ℚ) (hp : p ≤ (v : ℝ)) :
    p * (1-p) ≤ (bump v : ℝ) := by
  by_cases h : v ≤ 1/2
  · simp only [bump, min_eq_left h, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
    have hv : (v : ℝ) ≤ 1/2 := by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr h
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (show 0 ≤ 1-(v:ℝ)-p by linarith)]
  · rw [bump, min_eq_right (le_of_not_ge h)]
    norm_num
    nlinarith [sq_nonneg (p-1/2)]

private def bound₂ (l h : ℚ) : ℚ := min 1 (4*h*(1-l))
private def bound₃ (l h : ℚ) : ℚ := min 1 (h * max |3-4*l| |3-4*h| ^ 2)
private def bound₄ (l h : ℚ) : ℚ := min 1 (16*h*(1-l) * max |1-2*l| |1-2*h| ^ 2)
private def upper (l h : ℚ) : ℚ :=
  16*h*bound₂ l h*bump (4*bound₃ l h*bump (bound₄ l h))

private def covers (l h : ℚ) : ℕ → Bool
  | 0 => decide (upper l h < 3/2)
  | n+1 => decide (upper l h < 3/2) ||
      (covers l ((l+h)/2) n && covers ((l+h)/2) h n)

private lemma covers_sound {l h : ℚ} (n : ℕ) (hc : covers l h n = true)
    (x : ℝ) (hx₁ : (l:ℝ) ≤ x) (hx₂ : x ≤ (h:ℝ)) :
    ∃ l' h' : ℚ, (l':ℝ) ≤ x ∧ x ≤ (h':ℝ) ∧ upper l' h' < 3/2 := by
  induction n generalizing l h with
  | zero => exact ⟨l,h,hx₁,hx₂,of_decide_eq_true hc⟩
  | succ n ih =>
    simp only [covers, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | ⟨hl,hr⟩
    · exact ⟨l,h,hx₁,hx₂,hc⟩
    · by_cases hm : x ≤ (((l+h)/2 : ℚ):ℝ)
      · exact ih hl hx₁ hm
      · exact ih hr (le_of_not_ge hm) hx₂

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1600000 in
private lemma covers_unit : covers 0 1 11 = true := by decide +kernel

private lemma square_between {c d z : ℝ} (hl : d ≤ z) (hh : z ≤ c) :
    z^2 ≤ max |c| |d| ^ 2 := by
  apply sq_le_sq'
  · have hm := le_max_right |c| |d|
    linarith [neg_abs_le d]
  · exact hh.trans ((le_abs_self c).trans (le_max_left _ _))

private lemma sin_sq_le_one (x : ℝ) : Real.sin x ^ 2 ≤ 1 := by
  nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.cos x)]

private lemma sin_sq_double (x : ℝ) :
    Real.sin (2*x)^2 = 4*Real.sin x^2*(1-Real.sin x^2) := by
  rw [Real.sin_two_mul]
  linear_combination 4*Real.sin x^2*(Real.sin_sq_add_cos_sq x)

private lemma upper_bound (x y : ℝ) (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1)
    (l h : ℚ) (hl : (l:ℝ) ≤ Real.sin x ^ 2) (hh : Real.sin x ^ 2 ≤ (h:ℝ)) :
    let a := Real.sin x ^ 2
    let b := Real.sin (2*x) ^ 2
    let c := Real.sin (3*x) ^ 2
    let d := Real.sin (4*x) ^ 2
    let p := d*y
    let u := 4*c*(p*(1-p))
    16*a*b*(u*(1-u)) ≤ (upper l h : ℝ) := by
  let a := Real.sin x ^ 2
  let b := Real.sin (2*x) ^ 2
  let c := Real.sin (3*x) ^ 2
  let d := Real.sin (4*x) ^ 2
  have ha : 0 ≤ a := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  have hc : 0 ≤ c := sq_nonneg _
  have hd : 0 ≤ d := sq_nonneg _
  have ha' : a ≤ 1 := sin_sq_le_one _
  have hc' : c ≤ 1 := sin_sq_le_one _
  have hd' : d ≤ 1 := sin_sq_le_one _
  have hreal : 0 ≤ (h:ℝ) := ha.trans hh
  change (l:ℝ) ≤ a at hl
  change a ≤ (h:ℝ) at hh
  have hbEq : b = 4*a*(1-a) := sin_sq_double _
  have hcEq : c = a*(3-4*a)^2 := by unfold a c; rw [Real.sin_three_mul]; ring
  have hdEq : d = 16*a*(1-a)*(1-2*a)^2 := by
    unfold d
    rw [show 4*x = 2*(2*x) by ring, sin_sq_double]
    change 4*b*(1-b) = _
    rw [hbEq]
    ring
  have hfac : a*(1-a) ≤ (h:ℝ)*(1-(l:ℝ)) :=
    mul_le_mul hh (by linarith) (by linarith) hreal
  have hbU : b ≤ (bound₂ l h:ℝ) := by
    unfold bound₂
    push_cast
    apply le_min (sin_sq_le_one (2*x))
    linarith [hbEq]
  have hcU : c ≤ (bound₃ l h:ℝ) := by
    unfold bound₃
    push_cast
    apply le_min hc'
    rw [hcEq]
    exact mul_le_mul hh (square_between (by linarith) (by linarith)) (sq_nonneg _) hreal
  have hdU : d ≤ (bound₄ l h:ℝ) := by
    unfold bound₄
    push_cast
    apply le_min hd'
    rw [hdEq]
    apply mul_le_mul _ (square_between (by linarith) (by linarith)) (sq_nonneg _)
    · exact mul_nonneg (mul_nonneg (by norm_num) hreal) (by linarith)
    · linarith
  let p := d*y
  let u := 4*c*(p*(1-p))
  have hp : 0 ≤ p := mul_nonneg hd hy₀
  have hpU : p ≤ d := mul_le_of_le_one_right hd hy₁
  have hw : 0 ≤ p*(1-p) := mul_nonneg hp (by linarith)
  have hwU := bump_bound p (bound₄ l h) (hpU.trans hdU)
  have hu : 0 ≤ u := mul_nonneg (by positivity) hw
  have hu' : u ≤ 1 := by
    have hquarter : p*(1-p) ≤ 1/4 := by nlinarith [sq_nonneg (p-1/2)]
    calc
      u ≤ 4*1*(1/4) := mul_le_mul (by linarith) hquarter hw (by norm_num)
      _ = 1 := by norm_num
  have huU : u ≤ ((4*bound₃ l h*bump (bound₄ l h) : ℚ):ℝ) := by
    push_cast
    exact mul_le_mul (by linarith) hwU hw (by linarith)
  change 16*a*b*(u*(1-u)) ≤ _
  unfold upper
  push_cast only [Rat.cast_mul, Rat.cast_ofNat]
  apply mul_le_mul _ (bump_bound u _ huU) (mul_nonneg hu (by linarith))
  · exact mul_nonneg (by linarith) (hb.trans hbU)
  · exact mul_le_mul (by linarith) hbU hb (by linarith)

end OMA.S_mo_421887
open OMA.S_mo_421887

theorem OMA.solution : type_of% @OMA.S_mo_421887.main := by
  intro t x ht
  obtain ⟨l,h,hl,hh,hbound⟩ := covers_sound 11 covers_unit (Real.sin x ^ 2)
    (by simpa using sq_nonneg (Real.sin x)) (by simpa using sin_sq_le_one x)
  have hy : 4*t*(1-t) ≤ 1 := by nlinarith [sq_nonneg (2*t-1)]
  have hu := upper_bound x (4*t*(1-t)) (mul_nonneg (mul_nonneg (by norm_num) ht.1)
    (sub_nonneg.mpr ht.2)) hy l h hl hh
  have hreal : (upper l h : ℝ) < 3/2 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K:=ℝ)).mpr hbound
  apply lt_of_le_of_lt _ hreal
  dsimp only at hu ⊢
  apply le_trans _ hu
  apply le_of_eq
  ring
