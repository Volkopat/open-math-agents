import OMAStatements.S_mo_145467

/-! A proof of Wolfgang's nonhomogeneous fractional inequality (MathOverflow 145467).
The function x/(exp x - 1) is extended by continuity. Jensen's inequality
on the complement of each index gives a common set of comparison weights.
Credit: @Mapika. -/

open Real Finset Set Filter
open scoped Topology
namespace FractionalInequality

private noncomputable def expSlope (x : ℝ) : ℝ := (dslope Complex.exp 0 (x : ℂ)).re

private lemma slope_zero : expSlope 0 = 1 := by
  simp [expSlope, dslope_same, Complex.deriv_exp]

private lemma slope_ne {x : ℝ} (hx : x ≠ 0) : expSlope x = (exp x - 1) / x := by
  have h : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  simp [expSlope, dslope_of_ne _ h, slope_def_field, ← Complex.ofReal_exp,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div]

private lemma slope_pos (x : ℝ) : 0 < expSlope x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [slope_ne hx.ne]
    exact div_pos_of_neg_of_neg (sub_neg.mpr (exp_lt_one_iff.mpr hx)) hx
  · simp [slope_zero]
  · rw [slope_ne hx.ne']
    exact div_pos (sub_pos.mpr (one_lt_exp_iff.mpr hx)) hx

private noncomputable def bern (x : ℝ) : ℝ := (expSlope x)⁻¹

private lemma bern_pos (x : ℝ) : 0 < bern x := inv_pos.mpr (slope_pos x)
private lemma bern_zero : bern 0 = 1 := by simp [bern, slope_zero]
private lemma bern_ne {x : ℝ} (hx : x ≠ 0) : bern x = x / (exp x - 1) := by
  simp [bern, slope_ne hx]

private lemma bern_smooth : ContDiff ℝ 3 bern := by
  have hd : Differentiable ℂ (dslope Complex.exp 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope univ_mem).mpr Complex.differentiable_exp.differentiableOn
  have hc : ContDiff ℂ 3 (dslope Complex.exp 0) := hd.contDiff
  have hr : ContDiff ℝ 3 (dslope Complex.exp 0) := hc.restrict_scalars ℝ
  exact (Complex.reCLM.contDiff.comp (hr.comp Complex.ofRealCLM.contDiff)).inv
    (fun x => (slope_pos x).ne')

private lemma bracket_mono : Monotone (fun x : ℝ => (x-2)*exp x+x+2) := by
  apply monotone_of_deriv_nonneg (by fun_prop)
  intro x
  have d := (((hasDerivAt_id x).sub_const 2).mul (hasDerivAt_exp x) |>.add (hasDerivAt_id x)).add_const 2
  simp only [Pi.add_apply, Pi.mul_apply, id_eq] at d
  rw [d.deriv]
  have h := mul_le_mul_of_nonneg_right (add_one_le_exp (-x)) (exp_pos x).le
  rw [exp_neg, inv_mul_cancel₀ (exp_pos x).ne'] at h
  linarith

private lemma second_nonneg {x : ℝ} (hx : x ≠ 0) : 0 ≤ deriv (deriv bern) x := by
  let g := fun t : ℝ => (exp t - 1 - t * exp t) / (exp t - 1)^2
  have localDeriv (t : ℝ) (ht : t ≠ 0) : deriv bern t = g t := by
    have hd : exp t - 1 ≠ 0 := sub_ne_zero.mpr (fun h => ht ((exp_eq_one_iff _).mp h))
    have near : bern =ᶠ[𝓝 t] fun u => u / (exp u - 1) :=
      (eventually_ne_nhds ht).mono (fun u hu => bern_ne hu)
    have d := ((hasDerivAt_id t).div ((hasDerivAt_exp t).sub_const 1) hd).deriv
    change deriv (fun u : ℝ => u / (exp u - 1)) t = _ at d
    rw [near.deriv_eq, d]
    dsimp [g]
    ring
  have hnear : deriv bern =ᶠ[𝓝 x] g := (eventually_ne_nhds hx).mono localDeriv
  have hd : exp x - 1 ≠ 0 := sub_ne_zero.mpr (fun h => hx ((exp_eq_one_iff _).mp h))
  have de := (hasDerivAt_exp x).sub_const 1
  have dn := de.sub ((hasDerivAt_id x).mul (hasDerivAt_exp x))
  have hg := dn.div (de.pow 2) (pow_ne_zero 2 hd)
  rw [hnear.deriv_eq]
  change 0 ≤ deriv (fun t : ℝ => (exp t - 1 - t * exp t) / (exp t - 1)^2) x
  have d := hg.deriv
  change deriv (fun t : ℝ => (exp t - 1 - t * exp t) / (exp t - 1)^2) x = _ at d
  rw [d]
  suffices h : 0 ≤ exp x * ((x-2)*exp x+x+2) / (exp x-1)^3 by
    convert h using 1
    dsimp
    field_simp
    ring
  rcases lt_or_gt_of_ne hx with h | h
  · have hb := bracket_mono h.le
    simp at hb
    apply div_nonneg_iff.mpr ∘ Or.inr
    constructor
    · exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (by linarith)
    · have he : 0 ≤ 1 - exp x := by linarith [exp_lt_one_iff.mpr h]
      nlinarith [pow_nonneg he 3]
  · have hb := bracket_mono h.le
    simp at hb
    exact div_nonneg (mul_nonneg (exp_pos _).le (by linarith))
      (pow_nonneg (sub_nonneg.mpr (one_lt_exp_iff.mpr h).le) _)

private lemma bern_convex : ConvexOn ℝ univ bern := by
  have d : ContDiff ℝ 2 (deriv bern) := bern_smooth.deriv'
  have dd : Continuous (deriv (deriv bern)) := d.continuous_deriv (by decide)
  apply convexOn_univ_of_deriv2_nonneg (bern_smooth.differentiable (by decide))
    (d.differentiable (by decide))
  have hsub : ({(0:ℝ)}ᶜ : Set ℝ) ⊆ {x | 0 ≤ deriv (deriv bern) x} :=
    fun _ hx => second_nonneg hx
  have h := closure_minimal hsub (isClosed_le continuous_const dd)
  rw [closure_compl_singleton] at h
  exact fun x => h (mem_univ x)


/-- The share associated with an index and the weighted mean on its complement. -/
private noncomputable def share (p y z : ℝ) : ℝ :=
  p * bern y / (p * bern y + (1 - p) * bern z)

private lemma share_swap (p y z : ℝ) (hp : 0 < p) (hp' : p < 1) :
    share (1-p) z y = 1 - share p y z := by
  have hn : 0 < p*bern y + (1-p)*bern z := by
    exact add_pos (mul_pos hp (bern_pos _)) (mul_pos (sub_pos.mpr hp') (bern_pos _))
  simp only [share, sub_sub_cancel, add_comm ((1-p)*bern z)]
  field_simp
  ring

private lemma sum_share {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p y z : ι → ℝ) (hp : ∀ i, 0 < p i) (hp' : ∀ i, p i < 1)
    (hs : ∑ i, p i = 1) (hy : ∑ i, p i * y i = 0)
    (hz : ∀ i, p i * y i + (1-p i)*z i = 0) :
    1 ≤ ∑ i, share (p i) (y i) (z i) := by
  let W := ∑ i, p i * bern (y i)
  have hW : 0 < W := by
    have hne : (univ : Finset ι).Nonempty := by
      by_contra! he
      rw [he] at hs
      simp at hs
    exact sum_pos (fun i _ => mul_pos (hp i) (bern_pos _)) hne
  have each (i : ι) : p i * bern (y i) / W ≤ share (p i) (y i) (z i) := by
    let s := univ.erase i
    have hq : 0 < 1-p i := sub_pos.mpr (hp' i)
    have mass := univ.sum_erase_add p (mem_univ i)
    have moment := univ.sum_erase_add (fun j => p j*y j) (mem_univ i)
    rw [hs] at mass
    rw [hy] at moment
    have J := bern_convex.map_sum_le (t := s) (p := y) (w := fun j => p j / (1-p i))
      (fun j _ => (div_pos (hp j) hq).le)
      (by rw [← sum_div]; apply (div_eq_one_iff_eq hq.ne').mpr; dsimp [s]; linarith)
      (fun _ _ => mem_univ _)
    simp only [smul_eq_mul, div_mul_eq_mul_div, ← sum_div] at J
    have bary : (∑ j ∈ s, p j * y j) / (1-p i) = z i := by
      apply (div_eq_iff hq.ne').mpr
      dsimp [s]
      linarith [hz i]
    rw [bary] at J
    have cmp := (le_div_iff₀ hq).mp J
    have tot := univ.sum_erase_add (fun j => p j*bern (y j)) (mem_univ i)
    change (∑ j ∈ s, p j*bern (y j)) + p i*bern (y i) = W at tot
    exact div_le_div_of_nonneg_left (mul_pos (hp i) (bern_pos _)).le
      (add_pos (mul_pos (hp i) (bern_pos _)) (mul_pos hq (bern_pos _))) (by linarith)
  calc
    1 = ∑ i, p i * bern (y i) / W := by rw [← sum_div]; exact (div_self hW.ne').symm
    _ ≤ _ := sum_le_sum (fun i _ => each i)


private lemma bern_mul (x : ℝ) : bern x * (exp x-1) = x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [bern_ne hx, div_mul_cancel₀ _ (sub_ne_zero.mpr (fun h => hx ((exp_eq_one_iff _).mp h)))]

private lemma share_equation (p y z : ℝ) (hp : 0 < p) (hp' : p < 1)
    (balance : p*y+(1-p)*z=0) :
    share p y z * (exp y-exp z) = 1-exp z := by
  have den := add_pos (mul_pos hp (bern_pos y)) (mul_pos (sub_pos.mpr hp') (bern_pos z))
  unfold share
  field_simp
  linear_combination p * bern_mul y + (1-p) * bern_mul z + balance

open OMA.S_mo_145467 in
private lemma share_q (x t : ℝ) (hx : 0 < x) (ht : 1 < t) :
    share (1/t) ((t-1)*log x) (-log x) = q x t := by
  have ht0 : 0 < t := by linarith
  have hp : (0:ℝ) < 1/t := by positivity
  have hp' : (1:ℝ)/t < 1 := (div_lt_one ht0).mpr ht
  by_cases h : x = 1
  · simp [h, q, share, bern_zero]
  have eqn := share_equation (1/t) ((t-1)*log x) (-log x) hp hp' (by field_simp; ring)
  have e1 : exp ((t-1)*log x) * x = x ^ t := by
    nth_rw 2 [← exp_log hx]
    rw [← exp_add, rpow_def_of_pos hx]
    congr 1
    ring
  have e2 : exp (-log x) * x = 1 := by rw [exp_neg, exp_log hx, inv_mul_cancel₀ hx.ne']
  have hpow : x^t ≠ (1:ℝ) := by
    rcases lt_or_gt_of_ne h with hl | hl
    · exact (rpow_lt_one hx.le hl ht0).ne
    · exact (one_lt_rpow hl ht0).ne'
  rw [q, if_neg h, eq_div_iff (sub_ne_zero.mpr hpow.symm)]
  linear_combination -x * eqn + share (1/t) ((t-1)*log x) (-log x) * (e1-e2) + e2

open OMA.S_mo_145467 in
private lemma q_nonneg {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) : 0 ≤ q x t := by
  rcases lt_trichotomy x 1 with h | rfl | h
  · rw [q, if_neg h.ne]
    exact div_nonneg (by linarith) (by linarith [rpow_lt_one hx h ht])
  · simp [q, ht.le]
  · rw [q, if_neg h.ne']
    exact div_nonneg_iff.mpr (Or.inr ⟨by linarith, by linarith [one_lt_rpow h ht]⟩)

end FractionalInequality

open FractionalInequality OMA.S_mo_145467 in
theorem OMA.solution : type_of% @OMA.S_mo_145467.main := by
  intro n lam a hn hlam ha
  let k := lam * n
  let c := (lam-1/(n:ℝ))/(lam-1)
  let r := ∏ i, a i ^ c
  change q r lam ≤ ∑ i, q (a i) k
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hl : 0 < lam := by linarith
  have hk : 1 < k := by dsimp [k]; nlinarith [mul_nonneg (sub_nonneg.mpr hlam.le) (sub_nonneg.mpr hn1)]
  have hk0 : 0 < k := by linarith
  have hc : 0 < c := by
    have : 1/(n:ℝ) ≤ 1 := (div_le_one hn0).mpr hn1
    exact div_pos (by linarith) (by linarith)
  by_cases hpos : ∀ i, 0 < a i
  case neg =>
    push Not at hpos
    obtain ⟨i,hi⟩ := hpos
    have hz := le_antisymm hi (ha i)
    have hr : r = 0 := Finset.prod_eq_zero (mem_univ i) (by simp [hz, zero_rpow hc.ne'])
    have he := single_le_sum (f := fun j => q (a j) k)
      (fun j _ => q_nonneg (ha j) hk0) (mem_univ i)
    simpa [hr, hz, q, zero_rpow hl.ne', zero_rpow hk0.ne'] using he
  have hr : 0 < r := prod_pos (fun i _ => rpow_pos_of_pos (hpos i) _)
  let p : Fin (n+1) → ℝ := Fin.cases (1-1/lam) (fun _ => 1/k)
  let y : Fin (n+1) → ℝ := Fin.cases (-log r) (fun i => (k-1)*log (a i))
  let z : Fin (n+1) → ℝ := Fin.cases ((lam-1)*log r) (fun i => -log (a i))
  have pl : 0 < (1:ℝ)/lam := by positivity
  have pl' : (1:ℝ)/lam < 1 := (div_lt_one hl).mpr hlam
  have pk : 0 < (1:ℝ)/k := by positivity
  have pk' : (1:ℝ)/k < 1 := (div_lt_one hk0).mpr hk
  have posP : ∀ i, 0 < p i := Fin.cases (by simpa [p] using sub_pos.mpr pl') (fun _ => pk)
  have ltP : ∀ i, p i < 1 := Fin.cases (by simp [p, hl]) (fun _ => pk')
  have mass : ∑ i, p i = 1 := by
    rw [Fin.sum_univ_succ]
    simp [p, k, hn0.ne']
  have logr : log r = c * ∑ i, log (a i) := by
    rw [Real.log_prod (fun i _ => (rpow_pos_of_pos (hpos i) c).ne'), mul_sum]
    exact sum_congr rfl (fun i _ => log_rpow (hpos i) _)
  have balance : ∑ i, p i * y i = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [p, y, Fin.cases_zero, Fin.cases_succ, logr, ← mul_assoc, ← mul_sum]
    dsimp [k,c]
    field_simp [hl.ne', hn0.ne', (sub_pos.mpr hlam).ne']
    ring
  have complement : ∀ i, p i * y i + (1-p i)*z i = 0 := by
    refine Fin.cases ?_ (fun i => ?_)
    · simp [p,y,z]; field_simp; ring
    · simp [p,y,z]; field_simp; ring
  have hsum := sum_share p y z posP ltP mass balance complement
  rw [Fin.sum_univ_succ] at hsum
  simp only [p,y,z,Fin.cases_zero,Fin.cases_succ] at hsum
  rw [share_swap (1/lam) ((lam-1)*log r) (-log r) pl pl', share_q r lam hr hlam] at hsum
  simp_rw [fun i => share_q (a i) k (hpos i) hk] at hsum
  linarith
