import OMAStatements.S_oeis_a052952

/-! Proof of Wolfdieter Lang's complex Fibonacci floor conjecture.
The two terms in the numerator have moduli φ^m and exp(-πm)φ^(-m).
The triangle inequalities put the desired norm strictly between the two
real Binet bounds. One of those is a Fibonacci number, and their distance
is less than one. -/

namespace OMA.S_oeis_a052952

open Real

private lemma bounds (m : ℕ) (hm : 0 < m) :
    (goldenRatio^m-goldenRatio⁻¹^m)/√5 < ‖complexFib ((1+Complex.I)*(m:ℂ))‖ ∧
    ‖complexFib ((1+Complex.I)*(m:ℂ))‖ < (goldenRatio^m+goldenRatio⁻¹^m)/√5 := by
  let z : ℂ := (1+Complex.I)*(m:ℂ)
  let a := Complex.exp ((Real.log goldenRatio:ℂ)*z)
  let b := Complex.exp (Complex.I*Real.pi*z)*Complex.exp (-(Real.log goldenRatio:ℂ)*z)
  have ha : ‖a‖=goldenRatio^m := by
    simp [a,z,Complex.norm_exp,Complex.mul_re,mul_comm (Real.log goldenRatio),Real.exp_nat_mul,
      Real.exp_log goldenRatio_pos]
  have hb : ‖b‖=Real.exp (-Real.pi*m)*goldenRatio⁻¹^m := by
    rw [inv_pow]
    simp [b,z,Complex.norm_exp,Complex.mul_re, Complex.mul_im,
      mul_comm (Real.log goldenRatio),Real.exp_neg,Real.exp_nat_mul,Real.exp_log goldenRatio_pos]
  have hbs : ‖b‖ < goldenRatio⁻¹^m := by
    rw [hb]
    have hlt : Real.exp (-Real.pi*m)<1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (by exact_mod_cast hm))
    simpa using mul_lt_mul_of_pos_right hlt (pow_pos (inv_pos.mpr goldenRatio_pos) m)
  have hden : (2*(goldenRatio:ℂ)-1)=(√5:ℝ) := by
    push_cast
    ring
  change _ < ‖(a-b)/(2*(goldenRatio:ℂ)-1)‖ ∧ ‖(a-b)/(2*(goldenRatio:ℂ)-1)‖ < _
  rw [hden,norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  constructor
  · apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
    linarith [norm_sub_norm_le a b]
  · apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
    linarith [norm_sub_le a b]

end OMA.S_oeis_a052952

open OMA.S_oeis_a052952 Real

theorem OMA.solution : type_of% @OMA.S_oeis_a052952.main := by
  intro n
  obtain ⟨hl,hu⟩ := bounds (n+2) (by omega)
  push_cast at hl hu
  have hw : (goldenRatio^(n+2)+goldenRatio⁻¹^(n+2))/√5 <
      (goldenRatio^(n+2)-goldenRatio⁻¹^(n+2))/√5 + 1 := by
    have hsmall : goldenRatio⁻¹^(n+2) ≤ 1 := pow_le_one₀ (inv_pos.mpr goldenRatio_pos).le
      (inv_lt_one_of_one_lt₀ one_lt_goldenRatio).le
    have hs : 2 < √5 := Real.lt_sqrt_of_sq_lt (by norm_num)
    rw [div_add_one (by positivity),div_lt_div_iff_of_pos_right (by positivity)]
    linarith
  have hf := Real.coe_fib_eq (n+2)
  rw [show goldenConj= -goldenRatio⁻¹ by rw [inv_goldenRatio,neg_neg]] at hf
  apply Int.floor_eq_iff.mpr
  rcases Nat.even_or_odd (n+2) with he | ho
  · rw [he.neg_pow] at hf
    have hn : n%2=0 := by have := Nat.even_iff.mp he; omega
    rw [hn]; push_cast; constructor <;> linarith
  · rw [ho.neg_pow,sub_neg_eq_add] at hf
    have hn : n%2=1 := by have := Nat.odd_iff.mp ho; omega
    rw [hn]; push_cast; constructor <;> linarith
