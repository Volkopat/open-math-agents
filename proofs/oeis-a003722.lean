import OMAStatements.S_oeis_a003722
import Mathlib

/-!
# OEIS A003722: Bessel series for odd derivatives of `sin (sinh x)` at `0`

We factor `Complex.exp (Complex.I * Real.sinh x)` as the product of the two exponential series
`Complex.exp ((Complex.I / 2) * Complex.exp x)` and `Complex.exp ((-Complex.I / 2) * Complex.exp (-x))`,
multiply their Taylor series absolutely, and reindex `ℕ × ℕ` by `d = a - b` to express each slice
in terms of the modified Bessel function `besselI`. Taking imaginary parts yields the Jacobi-Anger
expansion `Real.sin (Real.sinh x) = ∑' k, 2 * (-1)^k * besselI (2k+1) 1 * Real.sinh ((2k+1) * x)`.
Using the factorial decay `besselI ν 1 ≤ Real.exp 1 / ν!`, we differentiate term-by-term on
`(-1, 1)` by induction on the derivative order and evaluate at `0`.
-/

namespace OMA.A003722Proof

open OMA.S_oeis_a003722

private lemma besselI_term_nonneg (ν m : ℕ) :
    0 ≤ ((1 : ℝ) / 2) ^ (2 * m + ν) / ((m.factorial : ℝ) * ((m + ν).factorial : ℝ)) := by
  positivity

private lemma besselI_term_le (ν m : ℕ) :
    ((1 : ℝ) / 2) ^ (2 * m + ν) / ((m.factorial : ℝ) * ((m + ν).factorial : ℝ)) ≤
      (1 / (ν.factorial : ℝ)) * ((1 : ℝ) ^ m / (m.factorial : ℝ)) := by
  have hpow : ((1 : ℝ) / 2) ^ (2 * m + ν) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hfac : (ν.factorial : ℝ) ≤ ((m + ν).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_left ν m)
  have hm_pos : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  have hν_pos : (0 : ℝ) < (ν.factorial : ℝ) := by positivity
  have hden : (m.factorial : ℝ) * (ν.factorial : ℝ) ≤
      (m.factorial : ℝ) * ((m + ν).factorial : ℝ) :=
    mul_le_mul_of_nonneg_left hfac hm_pos.le
  calc
    ((1 : ℝ) / 2) ^ (2 * m + ν) / ((m.factorial : ℝ) * ((m + ν).factorial : ℝ))
      ≤ 1 / ((m.factorial : ℝ) * ((m + ν).factorial : ℝ)) := by
        gcongr
    _ ≤ 1 / ((m.factorial : ℝ) * (ν.factorial : ℝ)) := by
        exact one_div_le_one_div_of_le (mul_pos hm_pos hν_pos) hden
    _ = (1 / (ν.factorial : ℝ)) * ((1 : ℝ) ^ m / (m.factorial : ℝ)) := by
        ring

private lemma besselI_summable (ν : ℕ) :
    Summable fun m : ℕ =>
      ((1 : ℝ) / 2) ^ (2 * m + ν) / ((m.factorial : ℝ) * ((m + ν).factorial : ℝ)) := by
  have hu : Summable fun m : ℕ => (1 / (ν.factorial : ℝ)) * ((1 : ℝ) ^ m / (m.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial 1).mul_left _
  exact Summable.of_nonneg_of_le (besselI_term_nonneg ν) (besselI_term_le ν) hu

private lemma besselI_nonneg (ν : ℕ) : 0 ≤ besselI ν 1 :=
  tsum_nonneg (besselI_term_nonneg ν)

private lemma besselI_le (ν : ℕ) : besselI ν 1 ≤ Real.exp 1 / (ν.factorial : ℝ) := by
  have hu : Summable fun m : ℕ => (1 / (ν.factorial : ℝ)) * ((1 : ℝ) ^ m / (m.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial 1).mul_left _
  have hle : besselI ν 1 ≤
      ∑' m : ℕ, (1 / (ν.factorial : ℝ)) * ((1 : ℝ) ^ m / (m.factorial : ℝ)) :=
    (besselI_summable ν).tsum_le_tsum (besselI_term_le ν) hu
  have hexp : (∑' m : ℕ, (1 : ℝ) ^ m / (m.factorial : ℝ)) = Real.exp 1 := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [tsum_mul_left, hexp] at hle
  simpa [div_eq_mul_inv, mul_comm] using hle

private def reindexEquiv : (ℕ ⊕ ℕ) × ℕ ≃ ℕ × ℕ where
  toFun
    | (Sum.inl ν, m) => (m + ν, m)
    | (Sum.inr ν, m) => (m, m + ν + 1)
  invFun p :=
    if p.2 ≤ p.1 then (Sum.inl (p.1 - p.2), p.2) else (Sum.inr (p.2 - p.1 - 1), p.1)
  left_inv
    | (Sum.inl ν, m) => by simp
    | (Sum.inr ν, m) => by
      have h : ¬ (m + ν + 1 ≤ m) := by omega
      simp [h]
      omega
  right_inv
    | (a, b) => by
      by_cases h : b ≤ a
      · simp [h]
      · simp [h]; omega

private def evenOddEquiv : ℕ ⊕ ℕ ≃ ℕ where
  toFun
    | Sum.inl k => 2 * k
    | Sum.inr k => 2 * k + 1
  invFun n := if n % 2 = 0 then Sum.inl (n / 2) else Sum.inr (n / 2)
  left_inv
    | Sum.inl k => by simp
    | Sum.inr k => by
      have h : ¬ ((2 * k + 1) % 2 = 0) := by omega
      simp
      omega
  right_inv n := by
    by_cases h : n % 2 = 0
    · simp [h]; omega
    · simp [h]; omega

private lemma tsum_sum_eq {α β M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] [T2Space M] {f : α ⊕ β → M}
    (hf1 : Summable (fun a => f (Sum.inl a))) (hf2 : Summable (fun b => f (Sum.inr b))) :
    (∑' x : α ⊕ β, f x) = (∑' a : α, f (Sum.inl a)) + (∑' b : β, f (Sum.inr b)) :=
  hf1.tsum_sum hf2

private lemma tsum_even_add_odd {f : ℕ → ℝ} (hf : Summable f) :
    (∑' n : ℕ, f n) = (∑' k : ℕ, f (2 * k)) + (∑' k : ℕ, f (2 * k + 1)) := by
  rw [← evenOddEquiv.tsum_eq]
  have hf1 : Summable (fun k : ℕ => f (evenOddEquiv (Sum.inl k))) :=
    hf.comp_injective (fun a b h => by dsimp [evenOddEquiv] at h; omega)
  have hf2 : Summable (fun k : ℕ => f (evenOddEquiv (Sum.inr k))) :=
    hf.comp_injective (fun a b h => by dsimp [evenOddEquiv] at h; omega)
  exact hf1.tsum_sum hf2

private lemma complex_exp_eq_tsum (z : ℂ) :
    Complex.exp z = ∑' n : ℕ, z ^ n / (n.factorial : ℂ) := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

private lemma complex_I_pow_even_im (k : ℕ) : (Complex.I ^ (2 * k)).im = 0 := by
  rw [pow_mul, Complex.I_sq]
  have h : ((-1 : ℂ) ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.ofReal_im]

private lemma complex_I_pow_odd_im (k : ℕ) : (Complex.I ^ (2 * k + 1)).im = (-1 : ℝ) ^ k := by
  rw [pow_succ, pow_mul, Complex.I_sq]
  rw [show ((-1 : ℂ) ^ k) * Complex.I = (((-1 : ℝ) ^ k : ℝ) : ℂ) * Complex.I by push_cast; rfl]
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma complex_neg_I_pow_even_im (k : ℕ) : ((-Complex.I) ^ (2 * k)).im = 0 := by
  rw [pow_mul, neg_sq, Complex.I_sq]
  have h : ((-1 : ℂ) ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.ofReal_im]

private lemma complex_neg_I_pow_odd_im (k : ℕ) :
    ((-Complex.I) ^ (2 * k + 1)).im = -((-1 : ℝ) ^ k) := by
  rw [pow_succ, pow_mul, neg_sq, Complex.I_sq]
  rw [show ((-1 : ℂ) ^ k) * (-Complex.I) = -((((-1 : ℝ) ^ k : ℝ) : ℂ) * Complex.I) by
    push_cast; ring]
  rw [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

private lemma summable_exp_mul_besselI (x : ℝ) :
    Summable fun ν : ℕ =>
      Complex.I ^ ν * Complex.exp ((ν : ℂ) * (x : ℂ)) * (besselI ν 1 : ℂ) := by
  have hu : Summable fun ν : ℕ =>
      Real.exp 1 * ((Real.exp x) ^ ν / (ν.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial (Real.exp x)).mul_left _
  refine Summable.of_norm_bounded hu (fun ν => ?_)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  have hexp_norm : ‖Complex.exp ((ν : ℂ) * (x : ℂ))‖ = (Real.exp x) ^ ν := by
    rw [show (ν : ℂ) * (x : ℂ) = (((ν : ℝ) * x : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [Real.exp_nat_mul]
  rw [hexp_norm, Complex.norm_real, Real.norm_of_nonneg (besselI_nonneg ν)]
  calc
    (Real.exp x) ^ ν * besselI ν 1
      ≤ (Real.exp x) ^ ν * (Real.exp 1 / (ν.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (besselI_le ν) (by positivity)
    _ = Real.exp 1 * ((Real.exp x) ^ ν / (ν.factorial : ℝ)) := by ring

private lemma summable_neg_exp_mul_besselI (x : ℝ) :
    Summable fun ν : ℕ =>
      (-Complex.I) ^ (ν + 1) * Complex.exp (-(((ν + 1 : ℕ) : ℂ) * (x : ℂ))) *
        (besselI (ν + 1) 1 : ℂ) := by
  have hu : Summable fun ν : ℕ =>
      Real.exp 1 * ((Real.exp (-x)) ^ (ν + 1) / ((ν + 1).factorial : ℝ)) :=
    ((Real.summable_pow_div_factorial (Real.exp (-x))).comp_injective Nat.succ_injective).mul_left _
  refine Summable.of_norm_bounded hu (fun ν => ?_)
  rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]
  have hexp_norm : ‖Complex.exp (-(((ν + 1 : ℕ) : ℂ) * (x : ℂ)))‖ = (Real.exp (-x)) ^ (ν + 1) := by
    rw [show -(((ν + 1 : ℕ) : ℂ) * (x : ℂ)) = ((((ν + 1 : ℕ) : ℝ) * (-x) : ℝ) : ℂ) by
      push_cast; ring]
    rw [← Complex.ofReal_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [Real.exp_nat_mul]
  rw [hexp_norm, Complex.norm_real, Real.norm_of_nonneg (besselI_nonneg (ν + 1))]
  calc
    (Real.exp (-x)) ^ (ν + 1) * besselI (ν + 1) 1
      ≤ (Real.exp (-x)) ^ (ν + 1) * (Real.exp 1 / ((ν + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (besselI_le (ν + 1)) (by positivity)
    _ = Real.exp 1 * ((Real.exp (-x)) ^ (ν + 1) / ((ν + 1).factorial : ℝ)) := by ring

private noncomputable def expTermPos (x : ℝ) (a : ℕ) : ℂ :=
  ((Complex.I / 2) * Complex.exp (x : ℂ)) ^ a / (a.factorial : ℂ)

private noncomputable def expTermNeg (x : ℝ) (b : ℕ) : ℂ :=
  ((-Complex.I / 2) * Complex.exp (-(x : ℂ))) ^ b / (b.factorial : ℂ)

private lemma pos_slice_eq (x : ℝ) (ν : ℕ) :
    (∑' m : ℕ, expTermPos x (m + ν) * expTermNeg x m) =
      Complex.I ^ ν * Complex.exp ((ν : ℂ) * (x : ℂ)) * (besselI ν 1 : ℂ) := by
  have hterm : ∀ m : ℕ,
      expTermPos x (m + ν) * expTermNeg x m =
        Complex.I ^ ν * Complex.exp ((ν : ℂ) * (x : ℂ)) *
          ((((1 : ℝ) / 2) ^ (2 * m + ν) /
            ((m.factorial : ℝ) * ((m + ν).factorial : ℝ)) : ℝ) : ℂ) := by
    intro m
    dsimp only [expTermPos, expTermNeg]
    rw [mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    have hexp : Complex.exp (((m + ν : ℕ) : ℂ) * (x : ℂ)) *
        Complex.exp ((m : ℂ) * (-(x : ℂ))) = Complex.exp ((ν : ℂ) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hI : (Complex.I / 2) ^ (m + ν) * (-Complex.I / 2) ^ m =
        Complex.I ^ ν * ((1 : ℂ) / 2) ^ (2 * m + ν) := by
      rw [show Complex.I / 2 = Complex.I * ((1 : ℂ) / 2) by ring,
        show -Complex.I / 2 = (-Complex.I) * ((1 : ℂ) / 2) by ring,
        mul_pow, mul_pow, pow_add Complex.I m ν, pow_add ((1 : ℂ) / 2) (2 * m) ν,
        two_mul, pow_add ((1 : ℂ) / 2) m m, pow_add ((1 : ℂ) / 2) m ν]
      have hpair : Complex.I ^ m * (-Complex.I) ^ m = 1 := by
        rw [← mul_pow, mul_neg, Complex.I_mul_I, neg_neg, one_pow]
      linear_combination
        (((1 : ℂ) / 2) ^ m * ((1 : ℂ) / 2) ^ m * ((1 : ℂ) / 2) ^ ν * Complex.I ^ ν) * hpair
    simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
    calc
      ((Complex.I / 2) ^ (m + ν) * Complex.exp (((m + ν : ℕ) : ℂ) * (x : ℂ)) /
          ((m + ν).factorial : ℂ)) *
        ((-Complex.I / 2) ^ m * Complex.exp ((m : ℂ) * -(x : ℂ)) / (m.factorial : ℂ))
        = ((Complex.I / 2) ^ (m + ν) * (-Complex.I / 2) ^ m) *
            (Complex.exp (((m + ν : ℕ) : ℂ) * (x : ℂ)) *
              Complex.exp ((m : ℂ) * -(x : ℂ))) /
            ((m.factorial : ℂ) * ((m + ν).factorial : ℂ)) := by ring
      _ = (Complex.I ^ ν * ((1 : ℂ) / 2) ^ (2 * m + ν)) *
            Complex.exp ((ν : ℂ) * (x : ℂ)) /
            ((m.factorial : ℂ) * ((m + ν).factorial : ℂ)) := by rw [hI, hexp]
      _ = Complex.I ^ ν * Complex.exp ((ν : ℂ) * (x : ℂ)) *
            (((1 : ℂ) / 2) ^ (2 * m + ν) /
              ((m.factorial : ℂ) * ((m + ν).factorial : ℂ))) := by ring
  simp_rw [hterm]
  rw [tsum_mul_left, ← Complex.ofReal_tsum]
  rfl

private lemma neg_slice_eq (x : ℝ) (ν : ℕ) :
    (∑' m : ℕ, expTermPos x m * expTermNeg x (m + ν + 1)) =
      (-Complex.I) ^ (ν + 1) * Complex.exp (-(((ν + 1 : ℕ) : ℂ) * (x : ℂ))) *
        (besselI (ν + 1) 1 : ℂ) := by
  have hterm : ∀ m : ℕ,
      expTermPos x m * expTermNeg x (m + ν + 1) =
        (-Complex.I) ^ (ν + 1) * Complex.exp (-(((ν + 1 : ℕ) : ℂ) * (x : ℂ))) *
          ((((1 : ℝ) / 2) ^ (2 * m + (ν + 1)) /
            ((m.factorial : ℝ) * ((m + (ν + 1)).factorial : ℝ)) : ℝ) : ℂ) := by
    intro m
    rw [show m + ν + 1 = m + (ν + 1) by omega]
    dsimp only [expTermPos, expTermNeg]
    rw [mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    have hexp : Complex.exp ((m : ℂ) * (x : ℂ)) *
        Complex.exp (((m + (ν + 1) : ℕ) : ℂ) * (-(x : ℂ))) =
        Complex.exp (-(((ν + 1 : ℕ) : ℂ) * (x : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hI : (Complex.I / 2) ^ m * (-Complex.I / 2) ^ (m + (ν + 1)) =
        (-Complex.I) ^ (ν + 1) * ((1 : ℂ) / 2) ^ (2 * m + (ν + 1)) := by
      rw [show Complex.I / 2 = Complex.I * ((1 : ℂ) / 2) by ring,
        show -Complex.I / 2 = (-Complex.I) * ((1 : ℂ) / 2) by ring,
        mul_pow, mul_pow, pow_add (-Complex.I) m (ν + 1),
        pow_add ((1 : ℂ) / 2) (2 * m) (ν + 1), two_mul,
        pow_add ((1 : ℂ) / 2) m m, pow_add ((1 : ℂ) / 2) m (ν + 1)]
      have hpair : Complex.I ^ m * (-Complex.I) ^ m = 1 := by
        rw [← mul_pow, mul_neg, Complex.I_mul_I, neg_neg, one_pow]
      linear_combination
        (((1 : ℂ) / 2) ^ m * ((1 : ℂ) / 2) ^ m * ((1 : ℂ) / 2) ^ (ν + 1) *
          (-Complex.I) ^ (ν + 1)) * hpair
    simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
    calc
      ((Complex.I / 2) ^ m * Complex.exp ((m : ℂ) * (x : ℂ)) / (m.factorial : ℂ)) *
        ((-Complex.I / 2) ^ (m + (ν + 1)) *
          Complex.exp (((m + (ν + 1) : ℕ) : ℂ) * -(x : ℂ)) /
          ((m + (ν + 1)).factorial : ℂ))
        = ((Complex.I / 2) ^ m * (-Complex.I / 2) ^ (m + (ν + 1))) *
            (Complex.exp ((m : ℂ) * (x : ℂ)) *
              Complex.exp (((m + (ν + 1) : ℕ) : ℂ) * -(x : ℂ))) /
            ((m.factorial : ℂ) * ((m + (ν + 1)).factorial : ℂ)) := by ring
      _ = ((-Complex.I) ^ (ν + 1) * ((1 : ℂ) / 2) ^ (2 * m + (ν + 1))) *
            Complex.exp (-(((ν + 1 : ℕ) : ℂ) * (x : ℂ))) /
            ((m.factorial : ℂ) * ((m + (ν + 1)).factorial : ℂ)) := by rw [hI, hexp]
      _ = (-Complex.I) ^ (ν + 1) * Complex.exp (-(((ν + 1 : ℕ) : ℂ) * (x : ℂ))) *
            (((1 : ℂ) / 2) ^ (2 * m + (ν + 1)) /
              ((m.factorial : ℂ) * ((m + (ν + 1)).factorial : ℂ))) := by ring
  simp_rw [hterm]
  rw [tsum_mul_left, ← Complex.ofReal_tsum]
  rfl

private lemma summable_norm_expTermPos (x : ℝ) :
    Summable fun a : ℕ => ‖expTermPos x a‖ :=
  (Real.summable_pow_div_factorial ‖(Complex.I / 2) * Complex.exp (x : ℂ)‖).congr fun a => by
    simp [expTermPos, norm_pow]

private lemma summable_norm_expTermNeg (x : ℝ) :
    Summable fun b : ℕ => ‖expTermNeg x b‖ :=
  (Real.summable_pow_div_factorial ‖(-Complex.I / 2) * Complex.exp (-(x : ℂ))‖).congr fun b => by
    simp [expTermNeg, norm_pow]

private lemma summable_expTerm_prod (x : ℝ) :
    Summable fun p : ℕ × ℕ => expTermPos x p.1 * expTermNeg x p.2 := by
  have h : Summable fun p : ℕ × ℕ => ‖expTermPos x p.1‖ * ‖expTermNeg x p.2‖ :=
    (summable_norm_expTermPos x).mul_of_nonneg (summable_norm_expTermNeg x)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hnorm : Summable fun p : ℕ × ℕ => ‖expTermPos x p.1 * expTermNeg x p.2‖ :=
    h.congr (fun p => (norm_mul _ _).symm)
  exact hnorm.of_norm

private lemma exp_I_sinh_eq_tsum (x : ℝ) :
    Complex.exp (Complex.I * (Real.sinh x : ℂ)) =
      (∑' ν : ℕ, Complex.I ^ ν * Complex.exp ((ν : ℂ) * (x : ℂ)) * (besselI ν 1 : ℂ)) +
      (∑' ν : ℕ, (-Complex.I) ^ (ν + 1) * Complex.exp (-(((ν + 1 : ℕ) : ℂ) * (x : ℂ))) *
        (besselI (ν + 1) 1 : ℂ)) := by
  have hprod_eq : Complex.exp (Complex.I * (Real.sinh x : ℂ)) =
      ∑' p : ℕ × ℕ, expTermPos x p.1 * expTermNeg x p.2 := by
    have harg : Complex.I * (Real.sinh x : ℂ) =
        (Complex.I / 2) * Complex.exp (x : ℂ) + (-Complex.I / 2) * Complex.exp (-(x : ℂ)) := by
      rw [Real.sinh_eq]
      push_cast
      ring
    have h1 : Complex.exp ((Complex.I / 2) * Complex.exp (x : ℂ)) =
        ∑' a : ℕ, expTermPos x a := by
      rw [complex_exp_eq_tsum]
      exact tsum_congr (fun _ => rfl)
    have h2 : Complex.exp ((-Complex.I / 2) * Complex.exp (-(x : ℂ))) =
        ∑' b : ℕ, expTermNeg x b := by
      rw [complex_exp_eq_tsum]
      exact tsum_congr (fun _ => rfl)
    rw [harg, Complex.exp_add, h1, h2]
    exact tsum_mul_tsum_of_summable_norm (summable_norm_expTermPos x) (summable_norm_expTermNeg x)
  let F : ℕ × ℕ → ℂ := fun p => expTermPos x p.1 * expTermNeg x p.2
  have hre_summable : Summable (fun q : (ℕ ⊕ ℕ) × ℕ => F (reindexEquiv q)) :=
    (reindexEquiv.summable_iff (f := F)).mpr (summable_expTerm_prod x)
  let g : ℕ ⊕ ℕ → ℂ := fun s => ∑' m : ℕ, F (reindexEquiv (s, m))
  have hiter : Complex.exp (Complex.I * (Real.sinh x : ℂ)) = ∑' s : ℕ ⊕ ℕ, g s := by
    rw [hprod_eq, ← reindexEquiv.tsum_eq F]
    exact hre_summable.tsum_prod
  have hg1 : ∀ ν : ℕ, g (Sum.inl ν) =
      Complex.I ^ ν * Complex.exp ((ν : ℂ) * (x : ℂ)) * (besselI ν 1 : ℂ) := by
    intro ν
    dsimp only [g, F, reindexEquiv]
    exact pos_slice_eq x ν
  have hg2 : ∀ ν : ℕ, g (Sum.inr ν) =
      (-Complex.I) ^ (ν + 1) * Complex.exp (-(((ν + 1 : ℕ) : ℂ) * (x : ℂ))) *
        (besselI (ν + 1) 1 : ℂ) := by
    intro ν
    dsimp only [g, F, reindexEquiv]
    exact neg_slice_eq x ν
  have hs1 : Summable (fun ν : ℕ => g (Sum.inl ν)) :=
    (summable_exp_mul_besselI x).congr (fun ν => (hg1 ν).symm)
  have hs2 : Summable (fun ν : ℕ => g (Sum.inr ν)) :=
    (summable_neg_exp_mul_besselI x).congr (fun ν => (hg2 ν).symm)
  rw [hiter, tsum_sum_eq hs1 hs2]
  simp_rw [hg1, hg2]

private lemma sin_sinh_eq_tsum (x : ℝ) :
    Real.sin (Real.sinh x) =
      ∑' k : ℕ, 2 * (-1 : ℝ) ^ k * besselI (2 * k + 1) 1 * Real.sinh ((2 * k + 1 : ℝ) * x) := by
  let c1 : ℕ → ℂ := fun ν =>
    Complex.I ^ ν * Complex.exp ((ν : ℂ) * (x : ℂ)) * (besselI ν 1 : ℂ)
  let c2 : ℕ → ℂ := fun ν =>
    (-Complex.I) ^ (ν + 1) * Complex.exp (-(((ν + 1 : ℕ) : ℂ) * (x : ℂ))) *
      (besselI (ν + 1) 1 : ℂ)
  have hc1 : Summable c1 := summable_exp_mul_besselI x
  have hc2 : Summable c2 := summable_neg_exp_mul_besselI x
  have hsum_split : Complex.exp (Complex.I * (Real.sinh x : ℂ)) =
      (∑' ν : ℕ, c1 ν) + (∑' ν : ℕ, c2 ν) := exp_I_sinh_eq_tsum x
  have him := congrArg Complex.imCLM hsum_split
  have hlhs : Complex.imCLM (Complex.exp (Complex.I * (Real.sinh x : ℂ))) =
      Real.sin (Real.sinh x) := by
    change (Complex.exp (Complex.I * (Real.sinh x : ℂ))).im = Real.sin (Real.sinh x)
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hlhs, map_add, Complex.imCLM.map_tsum hc1, Complex.imCLM.map_tsum hc2] at him
  have him1 : Summable (fun ν : ℕ => (c1 ν).im) := Complex.imCLM.summable hc1
  have him2 : Summable (fun ν : ℕ => (c2 ν).im) := Complex.imCLM.summable hc2
  have hc1_im : ∀ ν : ℕ,
      (c1 ν).im = (Complex.I ^ ν).im * Real.exp ((ν : ℝ) * x) * besselI ν 1 := by
    intro ν
    dsimp only [c1]
    rw [show (ν : ℂ) * (x : ℂ) = (((ν : ℝ) * x : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_exp, Complex.mul_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hc2_im : ∀ ν : ℕ,
      (c2 ν).im = ((-Complex.I) ^ (ν + 1)).im * Real.exp (-(((ν + 1 : ℕ) : ℝ) * x)) *
        besselI (ν + 1) 1 := by
    intro ν
    dsimp only [c2]
    rw [show -(((ν + 1 : ℕ) : ℂ) * (x : ℂ)) = ((-(((ν + 1 : ℕ) : ℝ) * x) : ℝ) : ℂ) by
        push_cast; ring,
      ← Complex.ofReal_exp, Complex.mul_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h1_odd : (∑' ν : ℕ, (c1 ν).im) =
      ∑' k : ℕ, (-1 : ℝ) ^ k * Real.exp ((2 * k + 1 : ℝ) * x) * besselI (2 * k + 1) 1 := by
    rw [tsum_even_add_odd him1]
    have heven : (∑' k : ℕ, (c1 (2 * k)).im) = 0 := by
      simp_rw [hc1_im, complex_I_pow_even_im, zero_mul, tsum_zero]
    rw [heven, zero_add]
    refine tsum_congr (fun k => ?_)
    rw [hc1_im, complex_I_pow_odd_im]
    push_cast
    ring
  have h2_odd : (∑' ν : ℕ, (c2 ν).im) =
      ∑' k : ℕ, (-((-1 : ℝ) ^ k)) * Real.exp (-((2 * k + 1 : ℝ) * x)) * besselI (2 * k + 1) 1 := by
    rw [tsum_even_add_odd him2]
    have hodd : (∑' k : ℕ, (c2 (2 * k + 1)).im) = 0 := by
      have hterm : ∀ k : ℕ, (c2 (2 * k + 1)).im = 0 := by
        intro k
        rw [hc2_im, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, complex_neg_I_pow_even_im]
        simp
      simp_rw [hterm, tsum_zero]
    rw [hodd, add_zero]
    refine tsum_congr (fun k => ?_)
    rw [hc2_im, complex_neg_I_pow_odd_im]
    push_cast
    ring
  have hs_pos : Summable fun k : ℕ =>
      (-1 : ℝ) ^ k * Real.exp ((2 * k + 1 : ℝ) * x) * besselI (2 * k + 1) 1 := by
    have hsub : Summable (fun k : ℕ => (c1 (2 * k + 1)).im) :=
      him1.comp_injective (fun a b h => by omega)
    refine hsub.congr (fun k => ?_)
    rw [hc1_im, complex_I_pow_odd_im]
    push_cast
    ring
  have hs_neg : Summable fun k : ℕ =>
      (-((-1 : ℝ) ^ k)) * Real.exp (-((2 * k + 1 : ℝ) * x)) * besselI (2 * k + 1) 1 := by
    have hsub : Summable (fun k : ℕ => (c2 (2 * k)).im) :=
      him2.comp_injective (fun a b h => by omega)
    refine hsub.congr (fun k => ?_)
    rw [hc2_im, complex_neg_I_pow_odd_im]
    push_cast
    ring
  change Real.sin (Real.sinh x) = (∑' ν : ℕ, (c1 ν).im) + (∑' ν : ℕ, (c2 ν).im) at him
  rw [him, h1_odd, h2_odd, ← hs_pos.tsum_add hs_neg]
  refine tsum_congr (fun k => ?_)
  rw [Real.sinh_eq]
  ring

private noncomputable def termDeriv (r k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * besselI (2 * k + 1) 1 *
    (((2 * k + 1 : ℝ) ^ r * Real.exp ((2 * k + 1 : ℝ) * x)) -
      ((-(2 * k + 1 : ℝ)) ^ r * Real.exp (-(2 * k + 1 : ℝ) * x)))

private noncomputable def termBound (r k : ℕ) : ℝ :=
  2 * Real.exp 1 * (r.factorial : ℝ) *
    ((Real.exp 2) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))

private lemma summable_termBound (r : ℕ) : Summable (termBound r) := by
  unfold termBound
  exact ((Real.summable_pow_div_factorial (Real.exp 2)).comp_injective
    (fun a b h => by omega)).mul_left _

private lemma hasDerivAt_termDeriv (r k : ℕ) (x : ℝ) :
    HasDerivAt (termDeriv r k) (termDeriv (r + 1) k x) x := by
  let c : ℝ := 2 * k + 1
  have h1 : HasDerivAt (fun y : ℝ => c ^ r * Real.exp (c * y)) (c ^ (r + 1) * Real.exp (c * x)) x := by
    have hmul : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (c * y)) (Real.exp (c * x) * c) x :=
      hmul.exp
    refine (hexp.const_mul (c ^ r)).congr_deriv ?_
    rw [pow_succ]
    ring
  have h2 : HasDerivAt (fun y : ℝ => (-c) ^ r * Real.exp ((-c) * y))
      ((-c) ^ (r + 1) * Real.exp ((-c) * x)) x := by
    have hmul : HasDerivAt (fun y : ℝ => (-c) * y) (-c) x := by
      simpa using (hasDerivAt_id x).const_mul (-c)
    have hexp : HasDerivAt (fun y : ℝ => Real.exp ((-c) * y)) (Real.exp ((-c) * x) * (-c)) x :=
      hmul.exp
    refine (hexp.const_mul ((-c) ^ r)).congr_deriv ?_
    rw [pow_succ]
    ring
  exact (h1.sub h2).const_mul ((-1 : ℝ) ^ k * besselI (2 * k + 1) 1)

private lemma norm_termDeriv_le (r k : ℕ) {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖termDeriv r k y‖ ≤ termBound r k := by
  let c : ℝ := 2 * k + 1
  have hc : 0 ≤ c := by positivity
  have h1 : c * y ≤ c := by nlinarith [hy.2]
  have h2 : -(c * y) ≤ c := by nlinarith [hy.1]
  have hexp1 : Real.exp (c * y) ≤ Real.exp c := Real.exp_le_exp.mpr h1
  have hexp2 : Real.exp (-(c * y)) ≤ Real.exp c := Real.exp_le_exp.mpr h2
  have hpow : c ^ r ≤ (r.factorial : ℝ) * Real.exp c := by
    have h := Real.pow_div_factorial_le_exp c hc r
    have hfac : (0 : ℝ) < (r.factorial : ℝ) := by positivity
    exact (div_le_iff₀ hfac).mp h |>.trans_eq (mul_comm _ _)
  have hdiff :
      |c ^ r * Real.exp (c * y) - (-c) ^ r * Real.exp (-(c * y))| ≤
        2 * (r.factorial : ℝ) * (Real.exp 2) ^ (2 * k + 1) := by
    have habs :
        |c ^ r * Real.exp (c * y) - (-c) ^ r * Real.exp (-(c * y))| ≤
          |c ^ r * Real.exp (c * y)| + |(-c) ^ r * Real.exp (-(c * y))| :=
      abs_sub _ _
    have ha1 : |c ^ r * Real.exp (c * y)| = c ^ r * Real.exp (c * y) :=
      abs_of_nonneg (mul_nonneg (pow_nonneg hc r) (Real.exp_pos _).le)
    have ha2 : |(-c) ^ r * Real.exp (-(c * y))| = c ^ r * Real.exp (-(c * y)) := by
      rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg hc, abs_of_nonneg (Real.exp_pos _).le]
    have hexp_sq : Real.exp c * Real.exp c = (Real.exp 2) ^ (2 * k + 1) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      dsimp only [c]
      push_cast
      ring
    calc
      |c ^ r * Real.exp (c * y) - (-c) ^ r * Real.exp (-(c * y))|
        ≤ c ^ r * Real.exp (c * y) + c ^ r * Real.exp (-(c * y)) := by linarith
      _ ≤ c ^ r * Real.exp c + c ^ r * Real.exp c := by
          gcongr
      _ = 2 * (c ^ r * Real.exp c) := by ring
      _ ≤ 2 * (((r.factorial : ℝ) * Real.exp c) * Real.exp c) := by
          gcongr
      _ = 2 * (r.factorial : ℝ) * (Real.exp c * Real.exp c) := by ring
      _ = 2 * (r.factorial : ℝ) * (Real.exp 2) ^ (2 * k + 1) := by rw [hexp_sq]
  rw [Real.norm_eq_abs]
  unfold termDeriv termBound
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (besselI_nonneg (2 * k + 1))]
  have hneg : -(2 * (k : ℝ) + 1) * y = -(c * y) := by dsimp only [c]; ring
  rw [show (2 * (k : ℝ) + 1) = c from rfl, hneg]
  calc
    besselI (2 * k + 1) 1 * |c ^ r * Real.exp (c * y) - (-c) ^ r * Real.exp (-(c * y))|
      ≤ (Real.exp 1 / ((2 * k + 1).factorial : ℝ)) *
          (2 * (r.factorial : ℝ) * (Real.exp 2) ^ (2 * k + 1)) := by
        exact mul_le_mul (besselI_le (2 * k + 1)) hdiff (abs_nonneg _) (by positivity)
    _ = 2 * Real.exp 1 * (r.factorial : ℝ) *
          ((Real.exp 2) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) := by ring

private lemma summable_termDeriv_zero (r : ℕ) : Summable (fun k : ℕ => termDeriv r k 0) :=
  Summable.of_norm_bounded (summable_termBound r)
    (fun k => norm_termDeriv_le r k (by simp))

private lemma iteratedDeriv_sin_sinh (r : ℕ) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      iteratedDeriv r (fun y : ℝ => Real.sin (Real.sinh y)) x = ∑' k : ℕ, termDeriv r k x := by
  induction r with
  | zero =>
    intro x _
    rw [iteratedDeriv_zero, sin_sinh_eq_tsum]
    refine tsum_congr (fun k => ?_)
    unfold termDeriv
    rw [Real.sinh_eq, pow_zero, pow_zero, one_mul, one_mul,
      show -(2 * (k : ℝ) + 1) * x = -((2 * (k : ℝ) + 1) * x) by ring]
    ring
  | succ r ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv r (fun y : ℝ => Real.sin (Real.sinh y)) =ᶠ[nhds x]
        (fun y => ∑' k : ℕ, termDeriv r k y) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo (-1) 1, isOpen_Ioo.mem_nhds hx, ih⟩
    rw [heq.deriv_eq]
    have hderiv := hasDerivAt_tsum_of_isPreconnected
      (summable_termBound (r + 1))
      isOpen_Ioo
      isPreconnected_Ioo
      (fun k y _ => hasDerivAt_termDeriv r k y)
      (fun k y hy => norm_termDeriv_le (r + 1) k hy)
      (by simp : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)
      (summable_termDeriv_zero r)
      hx
    exact hderiv.deriv

private lemma main_proof :
    ∀ n : ℕ,
      iteratedDeriv (2 * n + 1) (fun x : ℝ => Real.sin (Real.sinh x)) 0 =
        -2 * ∑' k : ℕ,
          (-1 : ℝ) ^ (k + 1) * ((2 * k + 1 : ℝ) ^ (2 * n + 1)) * besselI (2 * k + 1) 1 := by
  intro n
  rw [iteratedDeriv_sin_sinh (2 * n + 1) 0 (by simp)]
  have hterm : ∀ k : ℕ,
      termDeriv (2 * n + 1) k 0 =
        -2 * ((-1 : ℝ) ^ (k + 1) * ((2 * k + 1 : ℝ) ^ (2 * n + 1)) * besselI (2 * k + 1) 1) := by
    intro k
    unfold termDeriv
    rw [mul_zero, mul_zero, Real.exp_zero, mul_one, mul_one]
    have hodd : (-(2 * (k : ℝ) + 1)) ^ (2 * n + 1) = -((2 * (k : ℝ) + 1) ^ (2 * n + 1)) :=
      Odd.neg_pow ⟨n, rfl⟩ _
    rw [hodd, pow_succ]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]

end OMA.A003722Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a003722.main :=
  OMA.A003722Proof.main_proof
