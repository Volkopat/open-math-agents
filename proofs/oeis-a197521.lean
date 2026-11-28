import OMAStatements.S_oeis_a197521
import Mathlib

/-! Shifting the cosine equation by three and expanding the double and triple
angles produces the same cubic that controls positive sine roots near zero. -/
namespace Deldor14.FirstRoots
open Real Set OMA.S_oeis_a197521
private noncomputable def u (t : ℝ) := sin (π*t/6)
private noncomputable def f (t : ℝ) := 4*u t*(1-(u t)^2)-1
private theorem sine_factor (t : ℝ) :
    sin (π*t/6)-sin (π*t/3)^2 = -u t*f t := by
  unfold f u
  rw [show π*t/3=2*(π*t/6) by ring,sin_two_mul]
  linear_combination -4*(sin (π*t/6))^2*(sin_sq_add_cos_sq (π*t/6))
private theorem cosine_factor (t : ℝ) :
    cos (π*(3+t)/2)-cos (π*(3+t)/3)^2 = (u t+1)*f t := by
  unfold f u
  rw [show π*(3+t)/2=(3*(π*t/6)+π/2)+π by ring,cos_add_pi,cos_add_pi_div_two,
      neg_neg,sin_three_mul,show π*(3+t)/3=2*(π*t/6)+π by ring,cos_add_pi,cos_two_mul_eq_one_sub]
  ring
private theorem fzero : f 0 = -1 := by norm_num [f,u]
private theorem fone : f 1 = 1/2 := by norm_num [f,u,sin_pi_div_six]
private theorem least_root : ∃ t, IsLeast (Icc (0:ℝ) 1 ∩ {s | f s=0}) t := by
  have cont : Continuous f := by unfold f u;fun_prop
  apply (isCompact_Icc.inter_right (isClosed_eq cont continuous_const)).exists_isLeast
  have h : (0:ℝ) ∈ Icc (f 0) (f 1) := by rw [fzero,fone];constructor <;> norm_num
  obtain ⟨t,ht,zero⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) cont.continuousOn h
  exact ⟨t,ht,zero⟩
private theorem angle_bounds {t : ℝ} (lo : -3<t) (hi : t≤1) :
    -(π/2)<π*t/6 ∧ π*t/6≤π/2 := by
  constructor
  · nlinarith [mul_pos pi_pos (show 0<t+3 by linarith)]
  · nlinarith [mul_nonneg pi_pos.le (show 0≤1-t by linarith),pi_pos]
private theorem u_gt {t : ℝ} (lo : -3<t) (hi : t≤1) : -1<u t := by
  obtain ⟨a,b⟩ := angle_bounds lo hi
  simpa only [u,sin_neg,sin_pi_div_two] using sin_lt_sin_of_lt_of_le_pi_div_two le_rfl b a
private theorem positive_root {t : ℝ} (lo : -3<t) (hi : t≤1) (zero : f t=0) : 0<t := by
  by_contra! neg
  obtain ⟨left,_⟩ := angle_bounds lo hi
  have small : u t≤0 := sin_nonpos_of_nonpos_of_neg_pi_le
    (by exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos pi_pos.le neg) (by norm_num))
    (by linarith [pi_pos])
  have big : 0≤1-(u t)^2 := by
    dsimp [u]
    nlinarith [sin_sq_add_cos_sq (π*t/6),sq_nonneg (cos (π*t/6))]
  unfold f at zero
  nlinarith [mul_nonpos_of_nonpos_of_nonneg small big]

theorem result : type_of% @OMA.S_oeis_a197521.main := by
  obtain ⟨t,mem,least⟩ := least_root
  obtain ⟨⟨ht0,ht1⟩,zero⟩ := mem
  change f t=0 at zero
  have ht : 0<t := positive_root (by linarith) ht1 zero
  refine ⟨3+t,t,⟨⟨by linarith,?_⟩,?_⟩,⟨⟨ht,?_⟩,?_⟩,rfl⟩
  · have h := cosine_factor t
    rw [zero,mul_zero] at h
    linarith
  · intro x hx
    obtain ⟨xp,eq⟩ := hx
    by_contra! bad
    let s := x-3
    have es : x=3+s := by dsimp [s]; ring
    have lo : -3<s := by dsimp [s];linarith
    have hi : s≤1 := by dsimp [s];linarith
    rw [es] at eq
    have h := cosine_factor s
    rw [eq,sub_self] at h
    have root := (mul_eq_zero.mp h.symm).resolve_left (by linarith [u_gt lo hi])
    have positive := positive_root lo hi root
    have le := least (show s ∈ Icc (0:ℝ) 1 ∩ {v | f v=0} from ⟨⟨positive.le,hi⟩,root⟩)
    linarith
  · have h := sine_factor t
    rw [zero,mul_zero] at h
    linarith
  · intro s hs
    obtain ⟨sp,eq⟩ := hs
    by_contra! bad
    have hi : s≤1 := by linarith
    have angle := angle_bounds (by linarith : -3<s) hi
    have spos : 0<u s := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [angle.2,pi_pos])
    have h := sine_factor s
    rw [eq,sub_self] at h
    have root := (mul_eq_zero.mp h.symm).resolve_left (by linarith)
    have le := least (show s ∈ Icc (0:ℝ) 1 ∩ {v | f v=0} from ⟨⟨sp.le,hi⟩,root⟩)
    linarith
end Deldor14.FirstRoots
theorem OMA.solution : type_of% @OMA.S_oeis_a197521.main := Deldor14.FirstRoots.result
