import OMAStatements.S_mo_395730

-- Independent audit and proof-stage assembly: @CubeJerry.
-- uses note #100426
-- Source: https://github.com/connoranderson/open-math-agents/blob/933b148f48fb07f7f4a2860b2d5617edaea2fce5/proofs/mo-395730.lean

/-!
# The Gaussian kernel log determinant decreases with lengthscale

Source: Heinrich A, https://mathoverflow.net/questions/395730 (CC BY-SA 4.0).
Credit: @connoranderson.

The exponential series writes the quadratic form as a sum of nonnegative
squared moments and the Vandermonde matrix detects all nonzero vectors.
Jacobi's formula and cyclicity of trace then give the derivative sign.
The skew matrix XK−KX, for X the diagonal matrix of locations, accounts
for the sign of the trace.
-/

namespace OMA.S_mo_395730

open Finset Matrix

/-- A nonzero linear combination of distinct point masses has a nonzero moment
among its first n moments, by the Vandermonde determinant. -/
private lemma exp_quadratic_pos {n : ℕ} (u v : Fin n → ℝ) (hu : Function.Injective u)
    (hv : v ≠ 0) : 0 < ∑ i, ∑ j, v i * v j * Real.exp (u i*u j) := by
  classical
  let b (k : ℕ) := (∑ i, v i*u i^k)^2 / (k.factorial : ℝ)
  have hseries : HasSum b (∑ i, ∑ j, v i*v j*Real.exp (u i*u j)) := by
    have ht (i j : Fin n) : HasSum
        (fun k : ℕ => (v i*v j)*((u i*u j)^k / (k.factorial : ℝ)))
        (v i*v j*Real.exp (u i*u j)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact (NormedSpace.expSeries_div_hasSum_exp (u i*u j)).mul_left _
    have h := hasSum_sum (s := (univ : Finset (Fin n)))
      (fun i _ => hasSum_sum (s := (univ : Finset (Fin n))) (fun j _ => ht i j))
    convert h using 1
    funext k
    dsimp [b]
    rw [sq,Finset.sum_mul]
    simp only [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    ring
  obtain ⟨k,hk⟩ : ∃ k : Fin n, (∑ i, v i*u i^(k:ℕ)) ≠ 0 := by
    by_contra! h
    exact hv (Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hu h)
  rw [← hseries.tsum_eq]
  exact hseries.summable.tsum_pos (fun k => div_nonneg (sq_nonneg _) (by positivity))
    (k:ℕ) (show 0 < b k from div_pos (sq_pos_of_ne_zero hk) (by positivity))

lemma gaussian_posDef {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (σ θ : ℝ) (hσ : 0<σ) (hθ : 0<θ) : (gaussian x σ θ).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [gaussian, Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [show (x j-x i)^2=(x i-x j)^2 by ring]
  · intro v hv
    let u (i : Fin n) := x i/θ
    let w (i : Fin n) := v i * Real.exp (-(u i)^2/2)
    have hu : Function.Injective u := fun i j h => hx ((div_left_inj' hθ.ne').mp h)
    have hw : w ≠ 0 := by
      intro h
      apply hv
      funext i
      have hi : w i = 0 := congrFun h i
      exact (mul_eq_zero.mp hi).resolve_right (Real.exp_ne_zero _)
    have h := mul_pos hσ (exp_quadratic_pos u w hu hw)
    convert h using 1
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,gaussian,Matrix.of_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have he : -(x i-x j)^2/(2*θ^2) = (-(u i)^2/2+ -(u j)^2/2)+(u i*u j) := by
      dsimp [u]
      field_simp
      ring
    rw [he, Real.exp_add, Real.exp_add]
    dsimp [w]
    ring

end OMA.S_mo_395730

namespace OMA.S_mo_395730

open Matrix

private lemma det_deriv {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (h : ∀ i j, HasDerivAt (fun s => A s i j) (D i j) t) :
    HasDerivAt (fun s => (A s).det) ((A t).adjugate * D).trace t := by
  classical
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ :=
    { Matrix.detRowAlternating.toMultilinearMap with cont := continuous_id.matrix_det }
  have hd : HasDerivAt (fun s => fun i j => A s j i) (fun i j => D j i) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => h j i
  have e := (T.hasFDerivAt (fun i j => A t j i)).comp_hasDerivAt t hd
  have ht (s : ℝ) : T (fun i j => A s j i) = (A s).det := (A s).det_transpose
  change HasDerivAt (fun s => T (fun i j => A s j i)) _ t at e
  simp_rw [ht] at e
  convert e using 1
  rw [ContinuousMultilinearMap.linearDeriv_apply,Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  have he : T (Function.update (fun i j => A t j i) i (fun j => D j i)) =
      ((A t).updateCol i (fun j => D j i)).det := by
    change ((A t)ᵀ.updateRow i (fun j => D j i)).det = _
    rw [Matrix.updateRow_transpose,Matrix.det_transpose]
  rw [he,← Matrix.cramer_apply,Matrix.cramer_eq_adjugate_mulVec]
  rfl

end OMA.S_mo_395730

namespace OMA.S_mo_395730

open Matrix
open scoped MatrixOrder

private lemma trace_pos_product {n : ℕ} {J H : Matrix (Fin n) (Fin n) ℝ}
    (hJ : J.PosSemidef) (hH : H.PosSemidef) : 0 ≤ (J*H).trace := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hJ.nonneg
  rw [Matrix.star_eq_conjTranspose,← Matrix.trace_mul_cycle B H Bᴴ]
  exact (hH.mul_mul_conjTranspose_same B).trace_nonneg

private lemma trace_double_comm {n : ℕ} (K X : Matrix (Fin n) (Fin n) ℝ)
    (hk : K.PosDef) (hx : X.IsHermitian) :
    (K⁻¹*(X*(X*K-K*X)-(X*K-K*X)*X)).trace ≤ 0 := by
  let J := K⁻¹
  let C := X*K-K*X
  have hjk : J*K=1 := K.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hk.det_pos.ne')
  have hkj : K*J=1 := K.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hk.det_pos.ne')
  have hc : Cᴴ = -C := by
    simp only [C,Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,hx.eq,hk.1.eq,neg_sub]
  have hcom : J*X-X*J = J*C*J := by
    calc
      _ = J*X*(K*J) - (J*K)*X*J := by rw [hjk,hkj]; simp
      _ = _ := by dsimp only [C]; noncomm_ring
  have ht : (J*(X*C-C*X)).trace = ((J*X-X*J)*C).trace := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.trace_sub]
    rw [← Matrix.mul_assoc J X C,← Matrix.mul_assoc J C X,Matrix.trace_mul_cycle J C X]
  have hpos := trace_pos_product hk.inv.posSemidef (hk.inv.posSemidef.mul_mul_conjTranspose_same C)
  change 0 ≤ (J*(C*J*Cᴴ)).trace at hpos
  rw [hc,Matrix.mul_neg,Matrix.mul_neg,Matrix.trace_neg] at hpos
  change (J*(X*C-C*X)).trace ≤ 0
  rw [ht,hcom]
  simpa only [Matrix.mul_assoc,neg_nonneg] using hpos

end OMA.S_mo_395730

namespace OMA.S_mo_395730

open Matrix

private lemma pointwise_logdet {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (σ θ : ℝ) (hσ : 0<σ) (hθ : 0<θ) :
    DifferentiableAt ℝ (fun s => Real.log (gaussian x σ s).det) θ ∧
      deriv (fun s => Real.log (gaussian x σ s).det) θ ≤ 0 := by
  let K := gaussian x σ θ
  let X := Matrix.diagonal x
  let C := X*(X*K-K*X)-(X*K-K*X)*X
  let D := (θ^3)⁻¹ • C
  have hK : K.PosDef := gaussian_posDef x hx σ θ hσ hθ
  have hD (i j : Fin n) : D i j = (θ^3)⁻¹ * ((x i-x j)^2 * K i j) := by
    simp only [D,C,X,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply,Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    ring
  have hd (i j : Fin n) : HasDerivAt (fun s => gaussian x σ s i j) (D i j) θ := by
    rw [hD]
    let v := (x i-x j)^2
    have hv : HasDerivAt (fun s : ℝ => -v / (2*s^2)) (v/θ^3) θ := by
      have e := (hasDerivAt_const θ (-v)).div
        ((hasDerivAt_const θ (2:ℝ)).mul ((hasDerivAt_id θ).pow 2))
        (by change 2*θ^2 ≠ 0; positivity)
      apply e.congr_deriv
      dsimp
      field_simp
      ring
    apply (hv.exp.const_mul σ).congr_deriv
    change σ * (Real.exp (-v/(2*θ^2)) * (v/θ^3)) =
      (θ^3)⁻¹ * (v * (σ * Real.exp (-v/(2*θ^2))))
    ring
  have he := (det_deriv (gaussian x σ) D θ hd).log hK.det_pos.ne'
  refine ⟨he.differentiableAt,?_⟩
  rw [he.deriv]
  change (K.adjugate * D).trace / K.det ≤ 0
  have hi : K*K⁻¹=1 := K.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hK.det_pos.ne')
  have ha : K.adjugate = K.det • K⁻¹ := by
    calc
      _ = (K.adjugate*K)*K⁻¹ := by rw [Matrix.mul_assoc,hi,Matrix.mul_one]
      _ = _ := by rw [K.adjugate_mul,Matrix.smul_mul,Matrix.one_mul]
  have hn : (K⁻¹*C).trace ≤ 0 := trace_double_comm K X hK (Matrix.isHermitian_diagonal x)
  rw [ha,Matrix.smul_mul,Matrix.trace_smul]
  dsimp only [D]
  rw [Matrix.mul_smul,Matrix.trace_smul]
  simp only [smul_eq_mul]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hK.det_pos.le (mul_nonpos_of_nonneg_of_nonpos (by positivity) hn))
    hK.det_pos.le

end OMA.S_mo_395730

namespace OMA.S_mo_395730

lemma result {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x) (σ : ℝ) (hσ : 0<σ) :
    (∀ θ : ℝ, 0<θ → DifferentiableAt ℝ (fun s => Real.log (gaussian x σ s).det) θ ∧
      deriv (fun s => Real.log (gaussian x σ s).det) θ ≤ 0) ∧
    AntitoneOn (fun s => Real.log (gaussian x σ s).det) (Set.Ioi 0) := by
  have h := fun θ hθ => pointwise_logdet x hx σ θ hσ hθ
  refine ⟨h,antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_⟩
  · exact fun θ hθ => (h θ hθ).1.continuousAt.continuousWithinAt
  · exact fun θ hθ => (h θ (interior_subset hθ)).1.differentiableWithinAt
  · exact fun θ hθ => (h θ (interior_subset hθ)).2

end OMA.S_mo_395730

theorem OMA.solution : type_of% @OMA.S_mo_395730.main := by
  intro n x hx σ hσ
  exact OMA.S_mo_395730.result x hx σ hσ
