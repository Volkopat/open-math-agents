import OMAStatements.S_mo_285463

/-!
Credit: @connoranderson for the original proof, and @FrancoisCharroin for
its registered solution. The two polarizations follow Mikael de la Salle's
comment 705281 on MathOverflow question 285463. The real example adds the
determinant of a 2×2 matrix to its squared Frobenius norm.
-/

namespace OMA.S_mo_285463

open scoped TensorProduct
open TensorProduct

/-- Polarization for a complex sesquilinear form does not require Hermitian symmetry. -/
private lemma from_diag {X : Type*} [AddCommGroup X] [Module ℂ X] (B : X → X → ℂ)
    (hL : ∀ x y z, B (x+y) z = B x z+B y z)
    (hR : ∀ x y z, B x (y+z) = B x y+B x z)
    (hiL : ∀ x y, B (Complex.I • x) y = -Complex.I*B x y)
    (hiR : ∀ x y, B x (Complex.I • y) = Complex.I*B x y)
    (h : ∀ x, B x x=0) (x y : X) : B x y=0 := by
  have h1 := h (x+y)
  have h2 := h (x + Complex.I • y)
  simp only [hL,hR,hiL,hiR,h,mul_zero,zero_add,add_zero] at h1 h2
  have e : Complex.I*(B x y-B y x)=0 := by linear_combination h2
  have e' := (mul_eq_zero.mp e).resolve_left Complex.I_ne_zero
  linear_combination (h1+e')/2

private lemma complex_unique (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (B : (H ⊗[ℂ] K) →ₗ⋆[ℂ] (H ⊗[ℂ] K) →ₗ[ℂ] ℂ)
    (h : ∀ a b, B (a ⊗ₜ[ℂ] b) (a ⊗ₜ[ℂ] b)=inner ℂ a a * inner ℂ b b) : B=innerₛₗ ℂ := by
  let D := B-innerₛₗ ℂ
  have h0 (a : H) (b : K) : D (a ⊗ₜ[ℂ] b) (a ⊗ₜ[ℂ] b)=0 := by simp [D,h,mul_pow]
  have h1 (a a' : H) (b : K) : D (a ⊗ₜ[ℂ] b) (a' ⊗ₜ[ℂ] b)=0 := by
    apply from_diag (fun x y : H => D (x ⊗ₜ[ℂ] b) (y ⊗ₜ[ℂ] b)) _ _ _ _ (fun x => h0 x b) a a'
    · intro x y z; simp [add_tmul]
    · intro x y z; simp [add_tmul]
    · intro x y; simp [← smul_tmul',smul_eq_mul]
    · intro x y; simp [← smul_tmul',smul_eq_mul]
  have h2 (a a' : H) (b b' : K) : D (a ⊗ₜ[ℂ] b) (a' ⊗ₜ[ℂ] b')=0 := by
    apply from_diag (fun x y : K => D (a ⊗ₜ[ℂ] x) (a' ⊗ₜ[ℂ] y)) _ _ _ _ (fun x => h1 a a' x) b b'
    · intro x y z; simp [tmul_add]
    · intro x y z; simp [tmul_add]
    · intro x y; simp [tmul_smul,smul_eq_mul]
    · intro x y; simp [tmul_smul,smul_eq_mul]
  have hD : D=0 := by
    ext a b a' b'
    exact h2 a a' b b'
  exact sub_eq_zero.mp hD

end OMA.S_mo_285463
namespace OMA.S_mo_285463

open Matrix

private lemma real_counter : ∃ A : Matrix (Fin 4) (Fin 4) ℝ, A.PosDef ∧ A≠1 ∧
    ∀ x y : Fin 2 → ℝ, coords x y ⬝ᵥ (A *ᵥ coords x y) = (∑ i,(x i)^2)*(∑ i,(y i)^2) := by
  let A : Matrix (Fin 4) (Fin 4) ℝ := !![1,0,0,1/2;0,1,-(1/2),0;0,-(1/2),1,0;1/2,0,0,1]
  have hq (v : Fin 4 → ℝ) : v ⬝ᵥ (A *ᵥ v) =
      (v 0)^2+(v 1)^2+(v 2)^2+(v 3)^2+(v 0*v 3-v 1*v 2) := by
    simp [A,dotProduct,Matrix.mulVec,Fin.sum_univ_four]
    ring
  refine ⟨A,?_,?_,?_⟩
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j; fin_cases i <;> fin_cases j <;> norm_num [A,Matrix.conjTranspose_apply]
    · intro v hv
      rw [show star v=v by ext i; simp,hq]
      have H := (dotProduct_star_self_pos_iff (v := v)).mpr hv
      simp [dotProduct, Fin.sum_univ_four] at H
      nlinarith [sq_nonneg (v 0+v 3), sq_nonneg (v 1-v 2)]
  · intro h
    have e := congrFun₂ h 0 3
    change (1/2:ℝ)=0 at e
    norm_num at e
  · intro x y
    rw [hq]
    simp [coords,Fin.sum_univ_two]
    ring

end OMA.S_mo_285463

theorem OMA.solution : type_of% @OMA.S_mo_285463.main :=
  ⟨OMA.S_mo_285463.complex_unique, OMA.S_mo_285463.real_counter⟩
