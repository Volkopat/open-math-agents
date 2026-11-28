import OMAStatements.S_oeis_a143412
import Mathlib

open MeasureTheory ProbabilityTheory Polynomial

namespace OMA.A143412

lemma int_poly (p : ℝ[X]) : Integrable (fun x : ℝ => p.eval x) (gaussianReal 0 1) := by
  simp_rw [Polynomial.eval_eq_sum_range]
  refine integrable_finsetSum _ fun i _ => Integrable.const_mul ?_ _
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) (i : NNReal))
  have h2 : Integrable (fun x : ℝ => ‖id x‖ ^ i) (gaussianReal 0 1) :=
    MemLp.integrable_norm_pow' (by exact_mod_cast h)
  refine h2.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  simp

lemma int_pdf (q : ℝ[X]) : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * q.eval x) := by
  have h := int_poly q
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h
  refine h.congr (ae_of_all _ fun x => ?_)
  simp [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x)]

lemma pdf_deriv (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  rw [gaussianPDFReal_def]
  have h : HasDerivAt (fun y : ℝ => (√(2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2))
      ((√(2 * Real.pi))⁻¹ * (Real.exp (-x ^ 2 / 2) * (-x))) x := by
    have h' := ((((hasDerivAt_id' x).pow 2).neg.div_const 2).exp).const_mul (√(2 * Real.pi))⁻¹
    convert h' using 1
    · rfl
    · rfl
    · funext y; simp
    · show _ = (√(2 * Real.pi))⁻¹ * (Real.exp (-x ^ 2 / 2) * (-(((2 : ℕ) : ℝ) * x ^ (2 - 1) * 1) / 2))
      simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
      ring
  convert h using 1
  · funext y; simp
  · simp; ring

lemma stein (p : ℝ[X]) : ∫ x, x * p.eval x ∂gaussianReal 0 1 =
    ∫ x, (derivative p).eval x ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  have key : ∫ x : ℝ, (-x * gaussianPDFReal 0 1 x * p.eval x +
      gaussianPDFReal 0 1 x * (derivative p).eval x) = 0 := by
    refine integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun x => gaussianPDFReal 0 1 x * p.eval x) (fun x => ?_) ?_ (int_pdf p)
    · exact (pdf_deriv x).mul (p.hasDerivAt x)
    · have h1 := (int_pdf (X * p)).neg
      refine (h1.add (int_pdf (derivative p))).congr (ae_of_all _ fun x => ?_)
      simp; ring
  have h1 := int_pdf (X * p)
  have h2 := int_pdf (derivative p)
  have e : ∫ x : ℝ, (-x * gaussianPDFReal 0 1 x * p.eval x +
      gaussianPDFReal 0 1 x * (derivative p).eval x) =
      -(∫ x : ℝ, gaussianPDFReal 0 1 x * (X * p).eval x) +
        ∫ x : ℝ, gaussianPDFReal 0 1 x * (derivative p).eval x := by
    have t := integral_add h1.neg h2
    simp only [Pi.neg_apply, integral_neg] at t
    rw [← t]
    congr 1; ext x; simp; ring
  rw [e] at key
  simp only [smul_eq_mul, eval_mul, eval_X] at key ⊢
  linarith

noncomputable def I (m : ℤ) : ℝ := ∫ x, (Chebyshev.U ℝ m).eval x ∂gaussianReal 0 1
noncomputable def D (m : ℤ) : ℝ := ∫ x, (derivative (Chebyshev.U ℝ m)).eval x ∂gaussianReal 0 1

lemma int_eq {p q : ℝ[X]} (h : p = q) : ∫ x, p.eval x ∂gaussianReal 0 1 =
    ∫ x, q.eval x ∂gaussianReal 0 1 := by rw [h]

lemma r1 (m : ℤ) : I (m + 1) = 2 * D m - I (m - 1) := by
  have h := int_eq (Chebyshev.U_add_one ℝ m)
  have e : ∫ x, (2 * X * Chebyshev.U ℝ m - Chebyshev.U ℝ (m - 1)).eval x ∂gaussianReal 0 1 =
      2 * (∫ x, x * (Chebyshev.U ℝ m).eval x ∂gaussianReal 0 1) - I (m - 1) := by
    rw [I, ← integral_const_mul, ← integral_sub ((int_poly (X * Chebyshev.U ℝ m)).const_mul 2
      |>.congr (ae_of_all _ fun x => by simp)) (int_poly _)]
    congr 1; ext x; simp; ring
  rw [e, stein] at h
  exact h

lemma r2 (m : ℤ) : D (m + 2) - D m = 2 * (m + 2) * I (m + 1) := by
  have hp : derivative (Chebyshev.U ℝ (m + 2)) =
      derivative (Chebyshev.U ℝ m) + (2 * ((m : ℝ[X]) + 2)) * Chebyshev.U ℝ (m + 1) := by
    have h := congrArg derivative (Chebyshev.U_eq_two_mul_T_add_U ℝ m)
    rw [h]
    simp only [derivative_add, derivative_mul, derivative_ofNat, Chebyshev.T_derivative_eq_U,
      zero_mul, zero_add]
    rw [show m + 2 - 1 = m + 1 by ring]
    push_cast; ring
  have h := int_eq hp
  have e : ∫ x, (derivative (Chebyshev.U ℝ m) +
      (2 * ((m : ℝ[X]) + 2)) * Chebyshev.U ℝ (m + 1)).eval x ∂gaussianReal 0 1 =
      D m + 2 * (m + 2) * I (m + 1) := by
    rw [I, D, ← integral_const_mul, ← integral_add (int_poly _) ((int_poly _).const_mul _)]
    congr 1; ext x; simp
  rw [e] at h
  rw [D, h]; ring

lemma r3 (m : ℤ) : I (m + 4) = 4 * (m + 3) * I (m + 2) + I m := by
  have a1 := r1 (m + 3)
  have a2 := r1 (m + 1)
  have a3 := r2 (m + 1)
  rw [show m + 3 + 1 = m + 4 by ring, show m + 3 - 1 = m + 2 by ring] at a1
  rw [show m + 1 + 1 = m + 2 by ring, show m + 1 - 1 = m by ring] at a2
  rw [show m + 1 + 1 = m + 2 by ring, show m + 1 + 2 = m + 3 by ring] at a3
  push_cast at a3
  linarith

lemma main_aux (n : ℕ) : I (2 * (n : ℤ)) = (OMA.S_oeis_a143412.a n : ℝ) ∧
    I (2 * ((n + 1 : ℕ) : ℤ)) = (OMA.S_oeis_a143412.a (n + 1) : ℝ) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [I, OMA.S_oeis_a143412.a]
    · have h := r3 (-2)
      have h0 : I 0 = 1 := by simp [I]
      have hm : I (-2) = -1 := by simp [I]
      norm_num at h
      rw [h0, hm] at h
      simp [OMA.S_oeis_a143412.a]
      linarith
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h := r3 (2 * (k : ℤ))
    rw [show 2 * (((k + 1 + 1 : ℕ)) : ℤ) = 2 * (k : ℤ) + 4 by push_cast; ring, h,
      show 2 * (k : ℤ) + 2 = 2 * ((k + 1 : ℕ) : ℤ) by push_cast; ring, ih.1, ih.2]
    simp only [OMA.S_oeis_a143412.a]
    push_cast; ring

end OMA.A143412

theorem OMA.solution : type_of% @OMA.S_oeis_a143412.main := by
  intro n
  exact (OMA.A143412.main_aux n).1
