import OMAStatements.S_wpc_crouzeix_conjecture

/-! Adapted from OpenAI math, commit 3344da59991ed94f9ba711217b29c1d760badfa6, Apache License 2.0 (https://www.apache.org/licenses/LICENSE-2.0). DirectCrouzeix modules combined and adapted to the checker pin; scalar transfer and sharpness specialized below. -/

-- OAI/Analysis/DirectCrouzeix/Model.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

def numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ u : EuclideanSpace ℂ (Fin n), ‖u‖ = 1 ∧
    inner ℂ u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u) = z}

def polynomialValue {m d : ℕ} (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ)
    (z : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ∑ k : Fin (d + 1), z ^ (k : ℕ) • B k

def tensorEvaluation {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  ∑ k : Fin (d + 1), (A ^ (k : ℕ)) ⊗ₖ (B k)

def rangeMaximum {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  sSup ((fun z => ‖polynomialValue B z‖) '' numericalRange A)

def UniversalBound (c : ℝ) : Prop :=
  ∀ (n m d : ℕ), 0 < n → 0 < m →
    ∀ (A : Matrix (Fin n) (Fin n) ℂ)
      (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ),
      ‖tensorEvaluation A B‖ ≤ c * rangeMaximum A B

end DirectCrouzeix

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/NumericalRange.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

theorem numericalRange_eq_image {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRange A =
      (fun u : EuclideanSpace ℂ (Fin n) => inner ℂ u
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u)) '' Metric.sphere 0 1 := by
  ext z
  simp [numericalRange, Set.mem_image]

theorem isCompact_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    IsCompact (numericalRange A) := by
  rw [numericalRange_eq_image]
  exact (isCompact_sphere (0 : EuclideanSpace ℂ (Fin n)) 1).image
    (continuous_id.inner (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).continuous)

theorem numericalRange_nonempty {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) : (numericalRange A).Nonempty := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [numericalRange_eq_image]
  exact (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).image _

theorem norm_le_of_mem_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by
  obtain ⟨u, hu, rfl⟩ := hz
  calc
    ‖inner ℂ u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u)‖
        ≤ ‖u‖ * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖A‖ := by rw [hu, Matrix.l2_opNorm_toEuclideanCLM]; ring

theorem continuous_polynomialValue {m d : ℕ}
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) : Continuous (polynomialValue B) := by
  unfold polynomialValue
  exact continuous_finsetSum _ (fun k _ => (continuous_id.pow _).smul continuous_const)

theorem rangeMaximum_attained {n m d : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    ∃ z ∈ numericalRange A, ‖polynomialValue B z‖ = rangeMaximum A B := by
  have hc := (isCompact_numericalRange A).image (continuous_polynomialValue B).norm
  have hne := (numericalRange_nonempty hn A).image (fun z => ‖polynomialValue B z‖)
  obtain ⟨z, hz, he⟩ := hc.sSup_mem hne
  exact ⟨z, hz, he⟩

theorem norm_polynomialValue_le_rangeMaximum {n m d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖polynomialValue B z‖ ≤ rangeMaximum A B := by
  apply le_csSup
  · exact (isCompact_numericalRange A).bddAbove_image
      (continuous_polynomialValue B).norm.continuousOn
  · exact ⟨z, hz, rfl⟩

open scoped MatrixOrder ComplexOrder

end DirectCrouzeix

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/PositiveBlocks.lean
section
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

def hsSq {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) : ℝ :=
  (Matrix.trace (Mᴴ * M)).re

theorem hsSq_nonneg {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : 0 ≤ hsSq M := by
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self M).trace_nonneg).1

theorem re_trace_mul_nonneg {ι : Type u_5} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hC, Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  exact (Complex.nonneg_iff.mp (hB.mul_mul_conjTranspose_same C).trace_nonneg).1

theorem re_trace_block_comparison {ι : Type u_6} [Fintype ι] [DecidableEq ι]
    (D J : Matrix ι ι ℂ) (hD : D.PosSemidef) (hJ : J.IsHermitian) :
    0 ≤ (Matrix.trace (D * J * D * J)).re := by
  have hp := re_trace_mul_nonneg hD (hD.mul_mul_conjTranspose_same J)
  simpa only [hJ.eq, Matrix.mul_assoc] using hp

theorem positive_block_hsSq {ι : Type u_7} [Fintype ι] [DecidableEq ι]
    {U V Z : Matrix ι ι ℂ}
    (h : (Matrix.fromBlocks U Zᴴ Z V).PosSemidef) :
    2 * hsSq Z ≤ hsSq U + hsSq V := by
  let D := Matrix.fromBlocks U Zᴴ Z V
  let J : Matrix (Sum ι ι) (Sum ι ι) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  have hJ : J.IsHermitian := by
    exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_one (by simp)
      Matrix.isHermitian_one.neg
  have hU : U.IsHermitian := by
    have hh := h.isHermitian
    exact hh.submatrix Sum.inl
  have hV : V.IsHermitian := by
    have hh := h.isHermitian
    exact hh.submatrix Sum.inr
  have hp := re_trace_block_comparison D J h hJ
  have trace_blocks (A B C E : Matrix ι ι ℂ) :
      Matrix.trace (Matrix.fromBlocks A B C E) = Matrix.trace A + Matrix.trace E := by
    simp [Matrix.trace]
  have he : Matrix.trace (D * J * D * J) =
      Matrix.trace (U * U) + Matrix.trace (V * V) -
        2 * Matrix.trace (Zᴴ * Z) := by
    simp [D, J, Matrix.fromBlocks_multiply, trace_blocks,
      Matrix.trace_mul_comm Z Zᴴ]
    ring
  rw [he] at hp
  norm_num at hp
  simpa only [hsSq, hU.eq, hV.eq] using hp

end DirectCrouzeix

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/Resolvent.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

def quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) : ℂ :=
  inner ℂ u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u)

theorem quadratic_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    quadratic (A + B) u = quadratic A u + quadratic B u := by
  simp [quadratic]

theorem quadratic_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    quadratic (A - B) u = quadratic A u - quadratic B u := by
  simp [quadratic]

theorem quadratic_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    quadratic (c • A) u = c * quadratic A u := by
  simp [quadratic]

theorem quadratic_one {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) :
    quadratic 1 u = (‖u‖ : ℂ) ^ 2 := by
  simp [quadratic, inner_self_eq_norm_sq_to_K]

theorem quadratic_star {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    quadratic Aᴴ u = star (quadratic A u) := by
  simp only [quadratic, ← Matrix.star_eq_conjTranspose, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

theorem quadratic_vector_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) (c : ℂ) :
    quadratic A (c • u) = (star c * c) * quadratic A u := by
  simp [quadratic]
  ring

theorem quadratic_toLp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : Fin n → ℂ) :
    quadratic A (WithLp.toLp 2 u) = star u ⬝ᵥ (A *ᵥ u) := by
  simp [quadratic, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct_comm]

theorem posSemidef_of_unit_quadratic {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian)
    (hu : ∀ u : EuclideanSpace ℂ (Fin n), ‖u‖ = 1 → 0 ≤ (quadratic H u).re) :
    H.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  refine Complex.nonneg_iff.mpr ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
  rw [← quadratic_toLp]
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  change 0 ≤ (quadratic H v).re
  by_cases hv : v = 0
  · simp [hv, quadratic]
  let u : EuclideanSpace ℂ (Fin n) := ((‖v‖ : ℂ)⁻¹) • v
  have hun : ‖u‖ = 1 := norm_smul_inv_norm hv
  have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hv
  have he : (‖v‖ : ℂ) • u = v := by
    simp [u, smul_smul, hn]
  have hp := hu u hun
  rw [← he, quadratic_vector_smul]
  simpa [pow_two] using mul_nonneg (sq_nonneg ‖v‖) hp

theorem supported_matrix_posSemidef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z q : ℂ)
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (star q • (z • 1 - A) + q • (z • 1 - A)ᴴ).PosSemidef := by
  apply posSemidef_of_unit_quadratic
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      add_comm]
  intro u hu
  have hp := hs (quadratic A u) ⟨u, hu, rfl⟩
  rw [quadratic_add, quadratic_smul, quadratic_smul, quadratic_star,
    quadratic_sub, quadratic_smul, quadratic_one, hu]
  simp only [Complex.ofReal_one, one_pow, mul_one]
  have he : (star q * (z - quadratic A u) + q * star (z - quadratic A u)).re =
      2 * (star q * (z - quadratic A u)).re := by
    simp [Complex.mul_re]
    ring
  rw [he]
  linarith

theorem resolvent_congruence {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) (q : ℂ) :
    Bᴴ * ((q • B⁻¹) + (q • B⁻¹)ᴴ) * B = star q • B + q • Bᴴ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  have hstar : Bᴴ * (B⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_smul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [← Matrix.mul_assoc Bᴴ, hstar, Matrix.one_mul]
  exact add_comm _ _

theorem positive_resolvent_of_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z q : ℂ) (hB : IsUnit (z • 1 - A))
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (q • (z • 1 - A)⁻¹ + (q • (z • 1 - A)⁻¹)ᴴ).PosSemidef := by
  apply (Matrix.IsUnit.posSemidef_star_left_conjugate_iff hB).mp
  rw [Matrix.star_eq_conjTranspose, resolvent_congruence _ hB]
  exact supported_matrix_posSemidef A z q hs

theorem mem_numericalRange_of_eigenvector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {z : ℂ} {x : Fin n → ℂ} (hx : x ≠ 0) (he : A *ᵥ x = z • x) :
    z ∈ numericalRange A := by
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  have hv : v ≠ 0 := by simpa [v] using hx
  have he' : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A v = z • v := by
    simpa [v, Matrix.toEuclideanCLM_toLp] using congrArg (WithLp.toLp 2) he
  let u : EuclideanSpace ℂ (Fin n) := (‖v‖ : ℂ)⁻¹ • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
  have heu : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u = z • u := by
    simp [u, he', smul_smul, mul_comm]
  refine ⟨u, hu, ?_⟩
  rw [heu, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
  simp

theorem isUnit_resolvent_of_not_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {z : ℂ} (hz : z ∉ numericalRange A) : IsUnit (z • 1 - A) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  by_contra hh
  have hv : x - y ≠ 0 := sub_ne_zero.mpr hh
  have hzero : (z • 1 - A) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have he : A *ᵥ (x - y) = z • (x - y) := by
    symm
    apply sub_eq_zero.mp
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hzero
  exact hz (mem_numericalRange_of_eigenvector A hv he)

theorem positive_resolvent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z q : ℂ) (hz : z ∉ numericalRange A)
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (q • (z • 1 - A)⁻¹ + (q • (z • 1 - A)⁻¹)ᴴ).PosSemidef :=
  positive_resolvent_of_isUnit A z q (isUnit_resolvent_of_not_mem A hz) hs

end DirectCrouzeix

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/PolynomialCalculus.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

def exteriorCorrection (h q : ℂ → ℂ) (ζ μ : ℂ) : ℂ :=
  q ζ / (h ζ - h μ) - ζ / (ζ - μ)

def exteriorKernel (h q : ℂ → ℂ) (ζ μ : ℂ) : ℝ :=
  1 + (exteriorCorrection h q ζ μ).re + (star (exteriorCorrection h q ζ μ)).re

theorem re_circle_fraction {ζ μ : ℂ} (hζ : ‖ζ‖ = 1) (hμ : ‖μ‖ = 1)
    (hne : ζ ≠ μ) : 2 * (ζ / (ζ - μ)).re = 1 := by
  have hnζ : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using
      (show Complex.normSq ζ = 1 by rw [Complex.normSq_eq_norm_sq, hζ]; norm_num)
  have hnμ : μ.re ^ 2 + μ.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using
      (show Complex.normSq μ = 1 by rw [Complex.normSq_eq_norm_sq, hμ]; norm_num)
  have hd : Complex.normSq (ζ - μ) ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp (sub_ne_zero.mpr hne)
  rw [Complex.div_re]
  field_simp
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at *
  nlinarith

theorem exteriorKernel_nonneg_off_diagonal (h q : ℂ → ℂ)
    {ζ μ : ℂ} (hζ : ‖ζ‖ = 1) (hμ : ‖μ‖ = 1) (hne : ζ ≠ μ)
    (hs : 0 ≤ (star (q ζ) * (h ζ - h μ)).re) :
    0 ≤ exteriorKernel h q ζ μ := by
  have hfrac := re_circle_fraction hζ hμ hne
  have hp : 0 ≤ (q ζ / (h ζ - h μ)).re := by
    rw [Complex.div_re, ← add_div]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simpa [Complex.mul_re] using hs
  simp only [exteriorKernel, exteriorCorrection, Complex.sub_re, Complex.star_def,
    Complex.conj_re]
  linarith

def coefficientEmbedding (n m : ℕ) :
    Matrix (Fin m) (Fin m) ℂ →+*
      Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ where
  toFun B := (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ B
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_add' B C := Matrix.kronecker_add _ B C
  map_mul' B C := by
    simpa using Matrix.mul_kronecker_mul
      (1 : Matrix (Fin n) (Fin n) ℂ) 1 B C

def tensorPolynomial {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Polynomial (Matrix (Fin m) (Fin m) ℂ) →+*
      Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  Polynomial.eval₂RingHom' (coefficientEmbedding n m)
    (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) (by
      intro B
      change (1 ⊗ₖ B) * (A ⊗ₖ 1) = (A ⊗ₖ 1) * (1 ⊗ₖ B)
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp)

def coefficientPolynomial {m d : ℕ}
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    Polynomial (Matrix (Fin m) (Fin m) ℂ) :=
  ∑ k : Fin (d + 1), Polynomial.C (B k) * Polynomial.X ^ (k : ℕ)

theorem kronecker_pow_one {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) ^ k = (A ^ k) ⊗ₖ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, ← Matrix.mul_kronecker_mul]
    simp [pow_succ]

@[simp] theorem tensorPolynomial_C {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) :
    tensorPolynomial A (Polynomial.C B) = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ B := by
  exact Polynomial.eval₂_C _ _

@[simp] theorem tensorPolynomial_X {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    tensorPolynomial (m := m) A Polynomial.X = A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) := by
  exact Polynomial.eval₂_X _ _

theorem tensorPolynomial_coefficientPolynomial {n m d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    tensorPolynomial A (coefficientPolynomial B) = tensorEvaluation A B := by
  simp only [coefficientPolynomial, map_sum, map_mul, map_pow,
    tensorPolynomial_C, tensorPolynomial_X, kronecker_pow_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, tensorEvaluation]

theorem tensorPolynomial_mul {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (F G : Polynomial (Matrix (Fin m) (Fin m) ℂ)) :
    tensorPolynomial A (F * G) = tensorPolynomial A F * tensorPolynomial A G :=
  map_mul _ _ _

end DirectCrouzeix

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/HilbertSchmidt.lean
section
namespace OAI

universe u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25
  u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem hsSq_eq_sum_norm_sq {ι : Type u_8} {κ : Type u_9} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq M = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  simp only [hsSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

def hsVector {ι : Type u_10} {κ : Type u_11} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) :
    EuclideanSpace ℂ (ι × κ) := WithLp.toLp 2 (fun p => M p.1 p.2)

theorem hsSq_eq_norm_hsVector_sq {ι : Type u_12} {κ : Type u_13} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq M = ‖hsVector M‖ ^ 2 := by
  simp [hsSq_eq_sum_norm_sq, EuclideanSpace.norm_sq_eq, hsVector, Fintype.sum_prod_type]

theorem hsSq_conjTranspose {ι : Type u_14} {κ : Type u_15} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq Mᴴ = hsSq M := by
  simp only [hsSq_eq_sum_norm_sq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

theorem hsSq_smul {ι : Type u_16} {κ : Type u_17} [Fintype ι] [Fintype κ]
    (c : ℂ) (M : Matrix ι κ ℂ) : hsSq (c • M) = ‖c‖ ^ 2 * hsSq M := by
  simp only [hsSq_eq_sum_norm_sq, Matrix.smul_apply, smul_eq_mul, norm_mul,
    mul_pow, Finset.mul_sum]

def entryPair {ι : Type u_18} {κ : Type u_19} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) : ℂ := ∑ i, ∑ j, M i j * C i j

theorem entryPair_conj {ι : Type u_20} {κ : Type u_21} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : entryPair M (M.map star) = (hsSq M : ℂ) := by
  simp only [entryPair, Matrix.map_apply, hsSq_eq_sum_norm_sq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq]
  exact Complex.mul_conj _

theorem hsSq_map_star {ι : Type u_22} {κ : Type u_23} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq (M.map star) = hsSq M := by
  simp [hsSq_eq_sum_norm_sq]

theorem hsSq_mul_le {ι : Type u_24} {κ : Type u_25} {τ : Type u_26} [Fintype ι] [Fintype κ]
    [Fintype τ]
    [DecidableEq κ] (F : Matrix ι κ ℂ) (G : Matrix κ τ ℂ) :
    hsSq (F * G) ≤ ‖F‖ ^ 2 * hsSq G := by
  have col (M : Matrix ι τ ℂ) :
      hsSq M = ∑ j, ‖(WithLp.toLp 2 (fun i => M i j) : EuclideanSpace ℂ ι)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, hsSq_eq_sum_norm_sq]
    exact Finset.sum_comm
  have colG : hsSq G = ∑ j,
      ‖(WithLp.toLp 2 (fun i => G i j) : EuclideanSpace ℂ κ)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, hsSq_eq_sum_norm_sq]
    exact Finset.sum_comm
  rw [col, colG, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := Matrix.l2_opNorm_mulVec F (WithLp.toLp 2 (fun i => G i j))
  have h' : ‖(WithLp.toLp 2 (fun i => (F * G) i j) : EuclideanSpace ℂ ι)‖ ≤
      ‖F‖ * ‖(WithLp.toLp 2 (fun i => G i j) : EuclideanSpace ℂ κ)‖ := h
  calc
    _ ≤ (‖F‖ * ‖(WithLp.toLp 2 (fun i => G i j) : EuclideanSpace ℂ κ)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h' 2
    _ = _ := mul_pow _ _ _

theorem hsSq_mul_le_right {ι : Type u_27} {κ : Type u_28} {τ : Type u_29} [Fintype ι] [Fintype κ]
    [Fintype τ]
    [DecidableEq τ] [DecidableEq κ] (F : Matrix ι κ ℂ) (G : Matrix κ τ ℂ) :
    hsSq (F * G) ≤ hsSq F * ‖G‖ ^ 2 := by
  simpa only [← Matrix.conjTranspose_mul, hsSq_conjTranspose,
    Matrix.l2_opNorm_conjTranspose, mul_comm] using hsSq_mul_le Gᴴ Fᴴ

theorem entryPair_eq_inner {ι : Type u_30} {κ : Type u_31} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) :
    entryPair M C = inner ℂ (hsVector (M.map star)) (hsVector C) := by
  simp [entryPair, hsVector, PiLp.inner_apply, Fintype.sum_prod_type, mul_comm]

theorem norm_entryPair_sq_le {ι : Type u_32} {κ : Type u_33} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) : ‖entryPair M C‖ ^ 2 ≤ hsSq M * hsSq C := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (hsVector (M.map star)) (hsVector C)
  have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [← entryPair_eq_inner, mul_pow, ← hsSq_eq_norm_hsVector_sq,
    ← hsSq_eq_norm_hsVector_sq, hsSq_map_star] at h'
  exact h'

theorem norm_sum_entryPair_sq_le {ρ : Type u_34} {ι : Type u_35} {κ : Type u_36} [Fintype ρ]
    [Fintype ι] [Fintype κ]
    (M C : ρ → Matrix ι κ ℂ) :
    ‖∑ k, entryPair (M k) (C k)‖ ^ 2 ≤ (∑ k, hsSq (M k)) * ∑ k, hsSq (C k) := by
  have h := norm_entryPair_sq_le
    (fun (p : ρ × ι) (j : κ) => M p.1 p.2 j)
    (fun (p : ρ × ι) (j : κ) => C p.1 p.2 j)
  rw [hsSq_eq_sum_norm_sq (fun (p : ρ × ι) (j : κ) => M p.1 p.2 j),
    hsSq_eq_sum_norm_sq (fun (p : ρ × ι) (j : κ) => C p.1 p.2 j)] at h
  simpa only [entryPair, hsSq_eq_sum_norm_sq, Fintype.sum_prod_type] using h

end DirectCrouzeix

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/SingularPairs.lean
section
namespace OAI

universe u_37 u_38 u_39 u_40

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem positive_compression_blocks {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin m) ℂ) (hR : (R + Rᴴ).PosSemidef) :
    (Matrix.fromBlocks
      (Xᴴ * R * X + (Xᴴ * R * X)ᴴ)
      ((Yᴴ * R * X + (Xᴴ * R * Y)ᴴ)ᴴ)
      (Yᴴ * R * X + (Xᴴ * R * Y)ᴴ)
      (Yᴴ * R * Y + (Yᴴ * R * Y)ᴴ)).PosSemidef := by
  have h := hR.conjTranspose_mul_mul_same (Matrix.fromCols X Y)
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols] at h
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    add_comm] using h

theorem exists_norm_attainer {ι : Type u_37} [Fintype ι] [Nonempty ι]
    (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    ∃ x : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ ι) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1))
    T.continuous.norm.continuousOn
  have hx' : ‖x‖ = 1 := by simpa using hx
  refine ⟨x, hx', le_antisymm ?_ ?_⟩
  · simpa [hx'] using T.le_opNorm x
  · apply T.opNorm_le_bound (norm_nonneg _)
    intro v
    by_cases hv : v = 0
    · simp [hv]
    let u : EuclideanSpace ℂ ι := (‖v‖ : ℂ)⁻¹ • v
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
    have hm : ‖T u‖ ≤ ‖T x‖ := hmax (by simpa using hu)
    have he : ‖T u‖ = ‖T v‖ / ‖v‖ := by
      simp [u, norm_smul, div_eq_mul_inv, mul_comm]
    rw [he] at hm
    exact (div_le_iff₀ (norm_pos_iff.mpr hv)).mp hm

theorem exists_singular_pair {ι : Type u_38} [Fintype ι] [Nonempty ι]
    (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (hT : 0 < ‖T‖) :
    ∃ x y : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      T x = (‖T‖ : ℂ) • y ∧
      ContinuousLinearMap.adjoint T y = (‖T‖ : ℂ) • x := by
  obtain ⟨x, hx, hTx⟩ := exists_norm_attainer T
  let y : EuclideanSpace ℂ ι := (‖T‖ : ℂ)⁻¹ • T x
  have hn : (‖T‖ : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hy : ‖y‖ = 1 := by
    simp [y, norm_smul, hTx, ne_of_gt hT]
  have hxy : T x = (‖T‖ : ℂ) • y := by simp [y, smul_smul, hn]
  refine ⟨x, y, hx, hy, hxy, ?_⟩
  have ha : ‖ContinuousLinearMap.adjoint T y‖ ≤ ‖T‖ := by
    simpa [hy] using (ContinuousLinearMap.adjoint T).le_opNorm y
  have hi : inner ℂ (ContinuousLinearMap.adjoint T y) x = (‖T‖ : ℂ) := by
    rw [ContinuousLinearMap.adjoint_inner_left, hxy, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hy]
    simp
  have hd : ‖ContinuousLinearMap.adjoint T y - (‖T‖ : ℂ) • x‖ ^ 2 =
      ‖ContinuousLinearMap.adjoint T y‖ ^ 2 - ‖T‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hi]
    simp [norm_smul, hx]
    ring
  have he : ‖ContinuousLinearMap.adjoint T y - (‖T‖ : ℂ) • x‖ = 0 := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) ha 2
    nlinarith [sq_nonneg ‖ContinuousLinearMap.adjoint T y - (‖T‖ : ℂ) • x‖,
      norm_nonneg (ContinuousLinearMap.adjoint T y - (‖T‖ : ℂ) • x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

def matrixify {n m : ℕ} (x : EuclideanSpace ℂ (Fin n × Fin m)) :
    Matrix (Fin n) (Fin m) ℂ := fun i j => x (i, j)

@[simp] theorem hsVector_matrixify {n m : ℕ} (x : EuclideanSpace ℂ (Fin n × Fin m)) :
    hsVector (matrixify x) = x := by
  apply WithLp.ofLp_injective
  rfl

theorem tensor_entryPair {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) (X Y : Matrix (Fin n) (Fin m) ℂ) :
    inner ℂ (hsVector Y)
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (A ⊗ₖ C) (hsVector X)) =
      entryPair (Yᴴ * A * X) C := by
  simp only [hsVector, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toEuclideanCLM_toLp, dotProduct, Matrix.mulVec,
    Pi.star_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    entryPair, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs =>
    arg 2
    intro a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem entryPair_smul_right {ι : Type u_39} {κ : Type u_40} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) (c : ℂ) : entryPair M (c • C) = c * entryPair M C := by
  simp [entryPair, Finset.mul_sum, mul_left_comm]

end DirectCrouzeix

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/Duality.lean
section
namespace OAI

universe u_41 u_42 u_43 u_44 u_45

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem weighted_coefficient_dual {ρ : Type u_41} {ι : Type u_42} {κ : Type u_43}
    [Fintype ρ] [Fintype ι] [Fintype κ]
    (P : ρ → Matrix ι κ ℂ) (w : ρ → ℝ) (hw : ∀ k, 0 < w k)
    (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ C : ρ → Matrix ι κ ℂ,
      ‖∑ k, entryPair (P k) (C k)‖ ^ 2 ≤ b * ∑ k, w k * hsSq (C k)) :
    (∑ k, hsSq (P k) / w k) ≤ b := by
  let C : ρ → Matrix ι κ ℂ := fun k => ((w k : ℂ)⁻¹) • (P k).map star
  let s : ℝ := ∑ k, hsSq (P k) / w k
  have hs : 0 ≤ s := Finset.sum_nonneg (fun k _ => div_nonneg (hsSq_nonneg _) (hw k).le)
  have hp : (∑ k, entryPair (P k) (C k)) = (s : ℂ) := by
    simp only [C, entryPair_smul_right, entryPair_conj, s, Complex.ofReal_sum,
      Complex.ofReal_div]
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv]
    ring
  have he : (∑ k, w k * hsSq (C k)) = s := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [C, hsSq_smul, hsSq_map_star, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hw k)]
    field_simp
  have ht := h C
  rw [hp, he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] at ht
  by_cases hs0 : s = 0
  · change s ≤ b
    simpa [hs0] using hb
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    change s ≤ b
    apply (mul_le_mul_iff_left₀ hspos).mp
    nlinarith

open MeasureTheory

theorem weighted_integral_norm_sq_le {α : Type u_44} {E : Type u_45} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (k : α → ℝ) (u : α → E)
    (hk : ∀ x, 0 ≤ k x) (hki : Integrable k μ)
    (hui : Integrable (fun x => k x • u x) μ)
    (hsqi : Integrable (fun x => k x * ‖u x‖ ^ 2) μ)
    (hmass : ∫ x, k x ∂μ = 1) :
    ‖∫ x, k x • u x ∂μ‖ ^ 2 ≤ ∫ x, k x * ‖u x‖ ^ 2 ∂μ := by
  let v := ∫ x, k x • u x ∂μ
  have hii : Integrable (fun x => inner ℝ v (k x • u x)) μ :=
    (innerSL ℝ v).integrable_comp hui
  have hi : (∫ x, inner ℝ v (k x • u x) ∂μ) = ‖v‖ ^ 2 := by
    change (∫ x, (innerSL ℝ v) (k x • u x) ∂μ) = _
    rw [(innerSL ℝ v).integral_comp_comm hui]
    exact real_inner_self_eq_norm_sq v
  have hn : 0 ≤ ∫ x, k x * ‖u x - v‖ ^ 2 ∂μ :=
    integral_nonneg (fun x => mul_nonneg (hk x) (sq_nonneg _))
  have hexp : (fun x => k x * ‖u x - v‖ ^ 2) =
      fun x => (k x * ‖u x‖ ^ 2 - 2 * inner ℝ v (k x • u x)) + k x * ‖v‖ ^ 2 := by
    funext x
    rw [norm_sub_sq_real, inner_smul_right, real_inner_comm v (u x)]
    ring
  rw [hexp] at hn
  have hsubi : Integrable (fun x => k x * ‖u x‖ ^ 2 - 2 * inner ℝ v (k x • u x)) μ :=
    hsqi.sub (hii.const_mul 2)
  have hconsti : Integrable (fun x => k x * ‖v‖ ^ 2) μ := hki.mul_const _
  rw [integral_add hsubi hconsti, integral_sub hsqi (hii.const_mul 2),
    integral_const_mul, integral_mul_const, hi, hmass] at hn
  change ‖v‖ ^ 2 ≤ _
  linarith

end DirectCrouzeix

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/Sharpness.lean
section
namespace OAI

universe u_46

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem norm_entry_le_l2_opNorm {ι : Type u_46} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ ι := EuclideanSpace.single j 1
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
  have he : ‖e‖ = 1 := by simp [e]
  have hij : (T e) i = A i j := by
    change (A *ᵥ Pi.single j 1) i = _
    rw [Matrix.mulVec_single_one]
    rfl
  calc
    ‖A i j‖ = ‖(T e) i‖ := congrArg norm hij.symm
    _ ≤ ‖T e‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm _
    _ = ‖A‖ := by simp [T, he, Matrix.l2_opNorm_toEuclideanCLM]

def sharpnessMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 2; 0, 0]

def sharpnessCoefficients : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ := ![0, 1]

theorem norm_le_one_of_mem_sharpnessRange {z : ℂ}
    (hz : z ∈ numericalRange sharpnessMatrix) : ‖z‖ ≤ 1 := by
  obtain ⟨u, hu, rfl⟩ := hz
  have hsum : ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 = 1 := by
    simpa [hu, Fin.sum_univ_two] using (EuclideanSpace.norm_sq_eq u).symm
  have hev : inner ℂ u
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) sharpnessMatrix u) =
      2 * star (u 0) * u 1 := by
    simp [sharpnessMatrix, EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.ofLp_toEuclideanCLM, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  rw [hev]
  simp only [norm_mul, norm_star]
  norm_num
  nlinarith [sq_nonneg (‖u 0‖ - ‖u 1‖)]

@[simp] theorem sharpness_polynomialValue (z : ℂ) :
    polynomialValue (d := 1) sharpnessCoefficients z = z • 1 := by
  simp [polynomialValue, sharpnessCoefficients, Fin.sum_univ_two]

@[simp] theorem sharpness_tensorEvaluation :
    tensorEvaluation (d := 1) sharpnessMatrix sharpnessCoefficients =
      sharpnessMatrix ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [tensorEvaluation, sharpnessCoefficients, Fin.sum_univ_two]

theorem sharpness_rangeMaximum_le_one :
    rangeMaximum (d := 1) sharpnessMatrix sharpnessCoefficients ≤ 1 := by
  obtain ⟨z, hz, he⟩ := rangeMaximum_attained (by norm_num : 0 < 2)
    sharpnessMatrix (d := 1) sharpnessCoefficients
  rw [← he, sharpness_polynomialValue, norm_smul, norm_one, mul_one]
  exact norm_le_one_of_mem_sharpnessRange hz

theorem sharpness_tensor_norm_ge_two :
    2 ≤ ‖tensorEvaluation (d := 1) sharpnessMatrix sharpnessCoefficients‖ := by
  have h := norm_entry_le_l2_opNorm
    (sharpnessMatrix ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ)) (0, 0) (1, 0)
  rw [sharpness_tensorEvaluation]
  simpa [sharpnessMatrix, Matrix.kroneckerMap_apply] using h

theorem uniform_sharpness (c : ℝ) (hc : UniversalBound c) : 2 ≤ c := by
  have hmain := hc 2 1 1 (by norm_num) (by norm_num) sharpnessMatrix sharpnessCoefficients
  have hmax := sharpness_rangeMaximum_le_one
  have hlower := sharpness_tensor_norm_ge_two
  have hnonneg : 0 ≤ rangeMaximum (d := 1) sharpnessMatrix sharpnessCoefficients := by
    obtain ⟨z, hz, he⟩ := rangeMaximum_attained (by norm_num : 0 < 2)
      sharpnessMatrix (d := 1) sharpnessCoefficients
    rw [← he]
    exact norm_nonneg _
  have hcpos : 0 ≤ c := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hn) hnonneg
    linarith
  have hmul := mul_le_mul_of_nonneg_left hmax hcpos
  linarith

end DirectCrouzeix

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/CircleFourier.lean
section
namespace OAI

universe u_47 u_48 u_49 u_50 u_51 u_52 u_53 u_54 u_55 u_56 u_57 u_58 u_59 u_60 u_61 u_62 u_63 u_64
  u_65 u_66 u_67 u_68 u_69 u_70 u_71 u_72

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem continuous_integrable_compact {α : Type u_47} {E : Type u_48} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem continuous_integral_compact {α : Type u_49} {β : Type u_50} {E : Type u_51}
    [TopologicalSpace α] [FirstCountableTopology α] [LocallyCompactSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    [CompactSpace β] [SecondCountableTopology β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure β) [IsFiniteMeasure μ] {f : α → β → E}
    (hf : Continuous f.uncurry) : Continuous (fun x => ∫ y, f x y ∂μ) := by
  simpa using continuous_parametric_integral_of_continuous (μ := μ) hf isCompact_univ

theorem markov_kernel_contraction {α : Type u_52} {β : Type u_53} {E : Type u_54}
    [MetricSpace α] [MeasurableSpace α] [BorelSpace α] [CompactSpace α]
    [SecondCountableTopology α]
    [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [CompactSpace β]
    [SecondCountableTopology β]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (K : α → β → ℝ) (u : α → E)
    (hK : Continuous K.uncurry) (hu : Continuous u)
    (hpos : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∫ x, K x y ∂μ = 1)
    (hrow : ∀ x, ∫ y, K x y ∂ν = 1) :
    (∫ y, ‖∫ x, K x y • u x ∂μ‖ ^ 2 ∂ν) ≤ ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hKcol (y : β) : Continuous (fun x => K x y) :=
    hK.comp (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun y => ∫ x, K x y • u x ∂μ) := by
    apply continuous_integral_compact
    exact (hK.comp continuous_swap).smul (hu.comp continuous_snd)
  have hs : Integrable (fun p : α × β => K p.1 p.2 * ‖u p.1‖ ^ 2) (μ.prod ν) :=
    continuous_integrable_compact _ (hK.mul ((hu.comp continuous_fst).norm.pow 2))
  calc
    _ ≤ ∫ y, ∫ x, K x y * ‖u x‖ ^ 2 ∂μ ∂ν := by
      apply integral_mono (continuous_integrable_compact _ (hT.norm.pow 2))
        hs.integral_prod_right
      intro y
      exact weighted_integral_norm_sq_le μ (fun x => K x y) u (fun x => hpos x y)
        (continuous_integrable_compact _ (hKcol y))
        (continuous_integrable_compact _ ((hKcol y).smul hu))
        (continuous_integrable_compact _ ((hKcol y).mul (hu.norm.pow 2))) (hcol y)
    _ = ∫ x, ∫ y, K x y * ‖u x‖ ^ 2 ∂ν ∂μ := (integral_integral_swap hs).symm
    _ = _ := by simp_rw [integral_mul_const, hrow, one_mul]

abbrev BoundaryCircle := AddCircle (1 : ℝ)

abbrev circleMeasure : Measure BoundaryCircle := AddCircle.haarAddCircle

theorem scalar_circle_parseval (f : BoundaryCircle → ℂ) (hf : Continuous f) :
    HasSum (fun k : ℤ => ‖fourierCoeff f k‖ ^ 2)
      (∫ t, ‖f t‖ ^ 2 ∂circleMeasure) := by
  let F : C(BoundaryCircle, ℂ) := ⟨f, hf⟩
  have h := hasSum_sq_fourierCoeff (ContinuousMap.toLp 2 circleMeasure ℂ F)
  simp_rw [fourierCoeff_toLp] at h
  have hi : (∫ t, ‖(ContinuousMap.toLp 2 circleMeasure ℂ F) t‖ ^ 2 ∂circleMeasure) =
      ∫ t, ‖f t‖ ^ 2 ∂circleMeasure := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (𝕜 := ℂ) circleMeasure F]
      with t ht
    rw [ht]
    rfl
  rwa [hi] at h

theorem fourierCoeff_euclidean_apply {ι : Type u_55} [Fintype ι]
    (f : BoundaryCircle → EuclideanSpace ℂ ι) (hf : Continuous f)
    (k : ℤ) (i : ι) : (fourierCoeff f k) i = fourierCoeff (fun t => f t i) k := by
  have hi : Integrable (fun t => fourier (-k) t • f t) circleMeasure :=
    (continuous_integrable_compact _ hf).fourier_smul _
  exact ((EuclideanSpace.proj i).integral_comp_comm hi).symm

theorem euclidean_circle_parseval {ι : Type u_56} [Fintype ι]
    (f : BoundaryCircle → EuclideanSpace ℂ ι) (hf : Continuous f) :
    HasSum (fun k : ℤ => ‖fourierCoeff f k‖ ^ 2)
      (∫ t, ‖f t‖ ^ 2 ∂circleMeasure) := by
  have h (i : ι) := scalar_circle_parseval (fun t => f t i)
    ((PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).comp hf)
  have hs := hasSum_sum (s := Finset.univ) (fun i _ => h i)
  simp_rw [← fourierCoeff_euclidean_apply f hf] at hs
  simp_rw [EuclideanSpace.norm_sq_eq]
  have hi (i : ι) : Integrable (fun t => ‖f t i‖ ^ 2) circleMeasure :=
    continuous_integrable_compact _
      (((PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).comp hf).norm.pow 2)
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  exact hs

def hsCLM {ι : Type u_57} {κ : Type u_58} [Fintype ι] [Fintype κ] :
    Matrix ι κ ℂ →L[ℂ] EuclideanSpace ℂ (ι × κ) :=
  LinearMap.toContinuousLinearMap
    { toFun := hsVector
      map_add' := by intros; ext i; rfl
      map_smul' := by intros; ext i; rfl }

@[simp] theorem hsCLM_apply {ι : Type u_59} {κ : Type u_60} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : hsCLM A = hsVector A := rfl

theorem continuous_hsSq {ι : Type u_61} {κ : Type u_62} [Fintype ι] [Fintype κ] :
    Continuous (hsSq : Matrix ι κ ℂ → ℝ) := by
  change Continuous (fun M : Matrix ι κ ℂ => hsSq M)
  simp_rw [hsSq_eq_norm_hsVector_sq]
  exact hsCLM.continuous.norm.pow 2

theorem fourierCoeff_clm {E : Type u_63} {F : Type u_64} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (f : BoundaryCircle → E) (hf : Continuous f) (k : ℤ) :
    fourierCoeff (fun t => L (f t)) k = L (fourierCoeff f k) := by
  unfold fourierCoeff
  simp_rw [← map_smul]
  exact L.integral_comp_comm ((continuous_integrable_compact _ hf).fourier_smul _)

theorem matrix_circle_parseval {ι : Type u_65} {κ : Type u_66} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (f : BoundaryCircle → Matrix ι κ ℂ) (hf : Continuous f) :
    HasSum (fun k : ℤ => hsSq (fourierCoeff f k))
      (∫ t, hsSq (f t) ∂circleMeasure) := by
  have hp := euclidean_circle_parseval (fun t => hsCLM (f t)) (hsCLM.continuous.comp hf)
  simp_rw [fourierCoeff_clm hsCLM f hf, hsCLM_apply, ← hsSq_eq_norm_hsVector_sq] at hp
  exact hp

def compressionCLM {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin m) (Fin m) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun R => Yᴴ * R * X
      map_add' := by intros; simp [Matrix.mul_add,Matrix.add_mul]
      map_smul' := by intros; simp [Matrix.mul_smul,Matrix.smul_mul] }

@[simp] theorem compressionCLM_apply {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℂ)
    (R : Matrix (Fin n) (Fin n) ℂ) : compressionCLM X Y R = Yᴴ * R * X := rfl

theorem fourierCoeff_compression {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℂ)
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R) (k : ℤ) :
    fourierCoeff (fun t => Yᴴ * R t * X) k = Yᴴ * fourierCoeff R k * X :=
  fourierCoeff_clm (compressionCLM X Y) R hR k

def conjugateTransposeCLM {ι : Type u_67} {κ : Type u_68} [Fintype ι] [Fintype κ] :
    Matrix ι κ ℂ →L[ℝ] Matrix κ ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.conjTranspose
      map_add' := by intros; simp
      map_smul' := by intros; simp }

@[simp] theorem conjugateTransposeCLM_apply {ι : Type u_69} {κ : Type u_70} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : conjugateTransposeCLM A = Aᴴ := rfl

theorem fourierCoeff_star_matrix {ι : Type u_71} {κ : Type u_72} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (f : BoundaryCircle → Matrix ι κ ℂ) (hf : Continuous f) (k : ℤ) :
    fourierCoeff (fun t => (f t)ᴴ) k = (fourierCoeff f (-k))ᴴ := by
  unfold fourierCoeff
  have hh := conjugateTransposeCLM.integral_comp_comm
    ((continuous_integrable_compact _ hf).fourier_smul (-(-k)))
  simp only [conjugateTransposeCLM_apply] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards with t
  simp only [neg_neg,Matrix.conjTranspose_smul,starRingEnd_apply,fourier_neg]

end DirectCrouzeix

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/BoundaryEnergy.lean
section
namespace OAI

universe u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80 u_81 u_82 u_83 u_84 u_85 u_86

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem matrix_energy_split {ι : Type u_73} {κ : Type u_74} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (f : BoundaryCircle → Matrix ι κ ℂ) (hf : Continuous f) :
    (∫ t, hsSq (f t) ∂circleMeasure) =
      (∑' n : ℕ, hsSq (fourierCoeff f (n+1))) + hsSq (fourierCoeff f 0) +
      ∑' n : ℕ, hsSq (fourierCoeff f (-(n+1))) := by
  have hp := matrix_circle_parseval f hf
  rw [← hp.tsum_eq]
  apply tsum_of_add_one_of_neg_add_one
  · exact hp.summable.comp_injective (by intro i j he; exact_mod_cast (add_right_cancel he : (i : ℤ) = j))
  · exact hp.summable.comp_injective (by intro i j he; exact_mod_cast (add_right_cancel (neg_injective he) : (i : ℤ) = j))

@[simp] theorem hsSq_zero {ι : Type u_75} {κ : Type u_76} [Fintype ι] [Fintype κ] :
    hsSq (0 : Matrix ι κ ℂ) = 0 := by simp [hsSq_eq_sum_norm_sq]

theorem hsSq_add_self {ι : Type u_77} {κ : Type u_78} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    hsSq (A + A) = 4 * hsSq A := by
  rw [← two_smul ℂ A,hsSq_smul]
  norm_num

theorem fourierCoeff_add_star {ι : Type u_79} [Fintype ι] [DecidableEq ι]
    (P Q : BoundaryCircle → Matrix ι ι ℂ) (hP : Continuous P) (hQ : Continuous Q) (k : ℤ) :
    fourierCoeff (fun t => P t + (Q t)ᴴ) k =
      fourierCoeff P k + (fourierCoeff Q (-k))ᴴ := by
  have hQstar := conjugateTransposeCLM.continuous.comp hQ
  have hh := congrFun (fourierCoeff.add (continuous_integrable_compact _ hP)
    (continuous_integrable_compact _ hQstar)) k
  change fourierCoeff (fun t => P t + (Q t)ᴴ) k =
    fourierCoeff P k + fourierCoeff (fun t => (Q t)ᴴ) k at hh
  rwa [fourierCoeff_star_matrix Q hQ k] at hh

theorem anti_matrix_energy {ι : Type u_80} [Fintype ι] [DecidableEq ι]
    (P : BoundaryCircle → Matrix ι ι ℂ) (hP : Continuous P)
    (hpos : ∀ k : ℤ, 0 < k → fourierCoeff P k = 0) :
    (∫ t, hsSq (P t) ∂circleMeasure) = hsSq (fourierCoeff P 0) +
      ∑' n : ℕ, hsSq (fourierCoeff P (-(n+1))) := by
  rw [matrix_energy_split P hP]
  have hp : ∀ n : ℕ, fourierCoeff P (n+1) = 0 := fun n => hpos _ (by omega)
  simp only [hp,hsSq_zero,tsum_zero,zero_add]

theorem anti_diagonal_energy {ι : Type u_81} [Fintype ι] [DecidableEq ι]
    (P : BoundaryCircle → Matrix ι ι ℂ) (hP : Continuous P)
    (hpos : ∀ k : ℤ, 0 < k → fourierCoeff P k = 0)
    (hzero : (fourierCoeff P 0).IsHermitian) :
    (∫ t, hsSq (P t + (P t)ᴴ) ∂circleMeasure) =
      4 * (hsSq (fourierCoeff P 0) +
        (1/2 : ℝ) * ∑' n : ℕ, hsSq (fourierCoeff P (-(n+1)))) := by
  have hcont : Continuous (fun t => P t + (P t)ᴴ) :=
    hP.add (conjugateTransposeCLM.continuous.comp hP)
  rw [matrix_energy_split _ hcont]
  have hp : ∀ n : ℕ, fourierCoeff P (n+1) = 0 := fun n => hpos _ (by omega)
  simp only [fourierCoeff_add_star P P hP hP,neg_zero,hzero.eq,hp,neg_neg,
    Matrix.conjTranspose_zero,zero_add,add_zero,hsSq_conjTranspose,hsSq_add_self]
  ring

theorem anti_cross_energy {ι : Type u_82} [Fintype ι] [DecidableEq ι]
    (M L : BoundaryCircle → Matrix ι ι ℂ) (hM : Continuous M) (hL : Continuous L)
    (hMp : ∀ k : ℤ, 0 < k → fourierCoeff M k = 0)
    (hLp : ∀ k : ℤ, 0 < k → fourierCoeff L k = 0)
    (hzero : (fourierCoeff L 0)ᴴ = fourierCoeff M 0) :
    (∫ t, hsSq (M t) ∂circleMeasure) ≤
      ∫ t, hsSq (M t + (L t)ᴴ) ∂circleMeasure := by
  have hcont : Continuous (fun t => M t + (L t)ᴴ) :=
    hM.add (conjugateTransposeCLM.continuous.comp hL)
  rw [matrix_energy_split _ hcont,anti_matrix_energy M hM hMp]
  have hpM : ∀ n : ℕ, fourierCoeff M (n+1) = 0 := fun n => hMp _ (by omega)
  have hpL : ∀ n : ℕ, fourierCoeff L (n+1) = 0 := fun n => hLp _ (by omega)
  simp_rw [fourierCoeff_add_star M L hM hL,neg_zero,hzero,hpM,neg_neg,hpL,
    Matrix.conjTranspose_zero,zero_add,add_zero,hsSq_conjTranspose,hsSq_add_self]
  have hsum : 0 ≤ ∑' n : ℕ, hsSq (fourierCoeff L (-(n+1))) :=
    tsum_nonneg (fun _ => hsSq_nonneg _)
  nlinarith [hsSq_nonneg (fourierCoeff M 0)]

theorem finite_negative_bessel {ι : Type u_83} {κ : Type u_84} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (P : BoundaryCircle → Matrix ι κ ℂ) (hP : Continuous P) (N : ℕ) :
    (∑ k : Fin N, hsSq (fourierCoeff P (-(k : ℤ)))) ≤
      ∫ t, hsSq (P t) ∂circleMeasure := by
  classical
  let σ : Fin N → ℤ := fun k => -(k : ℤ)
  have hi : Function.Injective σ := by
    intro i j he
    apply Fin.ext
    exact_mod_cast neg_injective he
  have hp := matrix_circle_parseval P hP
  have hh := hp.summable.sum_le_tsum (Finset.univ.image σ) (fun _ _ => hsSq_nonneg _)
  rw [Finset.sum_image (fun i _ j _ he => hi he),hp.tsum_eq] at hh
  exact hh

def faberWeight (k : ℕ) : ℝ := if k = 0 then 1 else 2

theorem faberWeight_pos (k : ℕ) : 0 < faberWeight k := by
  unfold faberWeight
  split <;> norm_num

theorem weighted_sequence_dual {ι : Type u_85} {κ : Type u_86} [Fintype ι] [Fintype κ]
    (P : ℕ → Matrix ι κ ℂ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ N (C : Fin N → Matrix ι κ ℂ),
      ‖∑ k : Fin N, entryPair (P k) (C k)‖ ^ 2 ≤ b * ∑ k : Fin N, faberWeight k * hsSq (C k)) :
    hsSq (P 0) + (1/2 : ℝ) * ∑' n : ℕ, hsSq (P (n+1)) ≤ b := by
  have hsum : ∀ N, ∑ k ∈ Finset.range N, hsSq (P k) / faberWeight k ≤ b := by
    intro N
    have hh := weighted_coefficient_dual (fun k : Fin N => P k)
      (fun k => faberWeight k) (fun k => faberWeight_pos k) b hb (h N)
    rw [← Fin.sum_univ_eq_sum_range (fun k => hsSq (P k) / faberWeight k)]
    exact hh
  have hnon : ∀ k, 0 ≤ hsSq (P k) / faberWeight k :=
    fun k => div_nonneg (hsSq_nonneg _) (faberWeight_pos k).le
  have hsumm : Summable (fun k => hsSq (P k) / faberWeight k) :=
    summable_of_sum_range_le hnon hsum
  have hh := Real.tsum_le_of_sum_range_le hnon hsum
  rw [hsumm.tsum_eq_zero_add] at hh
  have hw0 : faberWeight 0 = 1 := by simp [faberWeight]
  have hw (n : ℕ) : faberWeight (n+1) = 2 := by simp [faberWeight]
  simp only [hw0,hw,div_one] at hh
  rw [tsum_div_const] at hh
  convert hh using 1 ; ring

end DirectCrouzeix

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/PolynomialEnergy.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

abbrev MatrixPolynomial (m : ℕ) := Polynomial (Matrix (Fin m) (Fin m) ℂ)

def matrixPolynomialValue {m : ℕ} (z : ℂ) :
    MatrixPolynomial m →+* Matrix (Fin m) (Fin m) ℂ :=
  Polynomial.eval₂RingHom' (RingHom.id _) (z • 1) (by
    intro C
    change C * (z • 1) = (z • 1) * C
    simp [])

@[simp] theorem matrixPolynomialValue_C {m : ℕ} (z : ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) : matrixPolynomialValue z (Polynomial.C C) = C := by
  exact Polynomial.eval₂_C _ _

@[simp] theorem matrixPolynomialValue_X {m : ℕ} (z : ℂ) :
    matrixPolynomialValue (m := m) z Polynomial.X = z • 1 := by
  exact Polynomial.eval₂_X _ _

theorem continuous_matrixPolynomialValue {m : ℕ} (G : MatrixPolynomial m) :
    Continuous (fun z => matrixPolynomialValue z G) :=
  (G.continuous_eval₂ (RingHom.id _)).comp (continuous_id.smul continuous_const)

def scalarMatrixPolynomial {m : ℕ} (p : Polynomial ℂ) : MatrixPolynomial m :=
  p.map (algebraMap ℂ (Matrix (Fin m) (Fin m) ℂ))

theorem matrixPolynomialValue_scalar {m : ℕ} (p : Polynomial ℂ) (z : ℂ) :
    matrixPolynomialValue (m := m) z (scalarMatrixPolynomial p) = p.eval z • 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [scalarMatrixPolynomial,Polynomial.map_add,map_add] at *
    rw [hp,hq,Polynomial.eval_add,add_smul]
  | monomial k c =>
    simp only [scalarMatrixPolynomial,← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,map_mul,map_pow,matrixPolynomialValue_C,matrixPolynomialValue_X,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    simp only [Algebra.algebraMap_eq_smul_one,smul_pow,one_pow,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,smul_smul]
    rw [mul_comm]

theorem tensorPolynomial_scalar {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (p : Polynomial ℂ) :
    tensorPolynomial (m := m) A (scalarMatrixPolynomial p) = (Polynomial.aeval A p) ⊗ₖ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [scalarMatrixPolynomial,Polynomial.map_add,map_add] at *
    rw [hp,hq,Matrix.add_kronecker]
  | monomial k c =>
    simp only [scalarMatrixPolynomial,← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,map_mul,map_pow,tensorPolynomial_C,tensorPolynomial_X,Polynomial.aeval_C,
      Polynomial.aeval_X,kronecker_pow_one,Algebra.algebraMap_eq_smul_one,
      Matrix.smul_kronecker,Matrix.kronecker_smul,← Matrix.mul_kronecker_mul,
      Matrix.smul_mul,Matrix.one_mul,Matrix.mul_one]

def faberPolynomial {m N : ℕ} (b : ℕ → Polynomial ℂ)
    (C : Fin N → Matrix (Fin m) (Fin m) ℂ) : MatrixPolynomial m :=
  ∑ k : Fin N, Polynomial.C (C k) * scalarMatrixPolynomial (b k)

theorem matrixPolynomialValue_faber {m N : ℕ} (b : ℕ → Polynomial ℂ)
    (C : Fin N → Matrix (Fin m) (Fin m) ℂ) (z : ℂ) :
    matrixPolynomialValue z (faberPolynomial b C) = ∑ k : Fin N, (b k).eval z • C k := by
  simp only [faberPolynomial,map_sum,map_mul,matrixPolynomialValue_C,matrixPolynomialValue_scalar,
    Matrix.mul_smul,Matrix.mul_one]

theorem tensorPolynomial_faber {n m N : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ) :
    tensorPolynomial A (faberPolynomial b C) = ∑ k : Fin N, Polynomial.aeval A (b k) ⊗ₖ C k := by
  simp only [faberPolynomial,map_sum,map_mul,tensorPolynomial_C,tensorPolynomial_scalar,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]

theorem faber_pairing {n m N : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (X Y : Matrix (Fin n) (Fin m) ℂ) :
    inner ℂ (hsVector Y) (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ)
      (tensorPolynomial A (faberPolynomial b C)) (hsVector X)) =
      ∑ k : Fin N, entryPair (Yᴴ * Polynomial.aeval A (b k) * X) (C k) := by
  simp only [tensorPolynomial_faber,map_sum,sum_apply,inner_sum,tensor_entryPair]

def polynomialEnergy {m : ℕ} (h : BoundaryCircle → ℂ) (G : MatrixPolynomial m) : ℝ :=
  ∫ t, hsSq (matrixPolynomialValue (h t) G) ∂circleMeasure

theorem polynomialEnergy_nonneg {m : ℕ} (h : BoundaryCircle → ℂ) (G : MatrixPolynomial m) :
    0 ≤ polynomialEnergy h G := integral_nonneg (fun _ => hsSq_nonneg _)

theorem polynomialEnergy_mul_le {m : ℕ} (h : BoundaryCircle → ℂ) (hh : Continuous h)
    (F G : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (h t) F‖ ≤ 1) :
    polynomialEnergy h (F * G) ≤ polynomialEnergy h G ∧
    polynomialEnergy h (G * F) ≤ polynomialEnergy h G := by
  have hint (H : MatrixPolynomial m) :
      Integrable (fun t => hsSq (matrixPolynomialValue (h t) H)) circleMeasure :=
    continuous_integrable_compact _
      (continuous_hsSq.comp ((continuous_matrixPolynomialValue H).comp hh))
  constructor
  · apply integral_mono (hint _) (hint _)
    intro t
    change hsSq (matrixPolynomialValue (h t) (F * G)) ≤ _
    rw [map_mul]
    exact (hsSq_mul_le _ _).trans (by
      have hn := pow_le_pow_left₀ (norm_nonneg _) (hF t) 2
      simpa using mul_le_mul_of_nonneg_right hn (hsSq_nonneg (matrixPolynomialValue (h t) G)))
  · apply integral_mono (hint _) (hint _)
    intro t
    change hsSq (matrixPolynomialValue (h t) (G * F)) ≤ _
    rw [map_mul]
    exact (hsSq_mul_le_right _ _).trans (by
      have hn := pow_le_pow_left₀ (norm_nonneg _) (hF t) 2
      simpa using mul_le_mul_of_nonneg_left hn (hsSq_nonneg (matrixPolynomialValue (h t) G)))

theorem cross_boundary_estimate {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (h : BoundaryCircle → ℂ)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (X Y : Matrix (Fin n) (Fin m) ℂ) (G : MatrixPolynomial m) :
    ‖inner ℂ (hsVector Y) (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ)
      (tensorPolynomial A G) (hsVector X))‖ ^ 2 ≤
      (∫ t, hsSq (Yᴴ * R t * X) ∂circleMeasure) * polynomialEnergy h G := by
  obtain ⟨N,C,rfl⟩ := hexpand G
  rw [faber_pairing]
  let M := fun t => Yᴴ * R t * X
  have hM : Continuous M := (compressionCLM X Y).continuous.comp hR
  have hMc (k : ℕ) : fourierCoeff M (-(k : ℤ)) = Yᴴ * Polynomial.aeval A (b k) * X := by
    rw [fourierCoeff_compression X Y R hR,hcoeff]
  have hb := finite_negative_bessel M hM N
  simp_rw [hMc] at hb
  have hb0 : 0 ≤ ∫ t, hsSq (M t) ∂circleMeasure := integral_nonneg (fun _ => hsSq_nonneg _)
  exact (norm_sum_entryPair_sq_le _ C).trans
    ((mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg (fun _ _ => hsSq_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (hlower N C) hb0))

theorem singular_ordered_pairings {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (F G : MatrixPolynomial m) (x y : EuclideanSpace ℂ (Fin n × Fin m)) (γ : ℝ)
    (hFx : Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F) x =
      (γ : ℂ) • y)
    (hFy : ContinuousLinearMap.adjoint
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F)) y =
      (γ : ℂ) • x) :
    inner ℂ y (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A (F * G)) x) =
      (γ : ℂ)
      * inner ℂ x (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A G) x) ∧
    inner ℂ y (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A (G * F)) x) =
      (γ : ℂ)
      * inner ℂ y (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A G) y) := by
  simp only [map_mul,mul_apply_eq_comp]
  constructor
  · rw [← ContinuousLinearMap.adjoint_inner_left,hFy,inner_smul_left]
    simp
  · rw [hFx,map_smul,inner_smul_right]

theorem singular_diagonal_estimates {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (h : BoundaryCircle → ℂ) (hh : Continuous h)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (hupper : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      polynomialEnergy h (faberPolynomial b C) ≤ ∑ k : Fin N, faberWeight k * hsSq (C k))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (F : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (h t) F‖ ≤ 1)
    (X Y : Matrix (Fin n) (Fin m) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hFx : Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F) (hsVector X) =
      (γ : ℂ) • hsVector Y)
    (hFy : ContinuousLinearMap.adjoint
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F)) (hsVector Y) =
      (γ : ℂ) • hsVector X) :
    let a := ∫ t, hsSq (Yᴴ * R t * X) ∂circleMeasure
    (hsSq (Xᴴ * Polynomial.aeval A (b 0) * X) + (1/2 : ℝ) *
      ∑' k : ℕ, hsSq (Xᴴ * Polynomial.aeval A (b (k+1)) * X) ≤ a / γ^2) ∧
    (hsSq (Yᴴ * Polynomial.aeval A (b 0) * Y) + (1/2 : ℝ) *
      ∑' k : ℕ, hsSq (Yᴴ * Polynomial.aeval A (b (k+1)) * Y) ≤ a / γ^2) := by
  dsimp only
  let a := ∫ t, hsSq (Yᴴ * R t * X) ∂circleMeasure
  have ha : 0 ≤ a := integral_nonneg (fun _ => hsSq_nonneg _)
  have hdiv : 0 ≤ a / γ^2 := div_nonneg ha (sq_nonneg _)
  have htest (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ) :=
    singular_ordered_pairings A F (faberPolynomial b C) (hsVector X) (hsVector Y) γ hFx hFy
  have hbound (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ) :
      (‖∑ k : Fin N, entryPair (Xᴴ * Polynomial.aeval A (b k) * X) (C k)‖^2 ≤
        (a / γ^2) * ∑ k : Fin N, faberWeight k * hsSq (C k)) ∧
      (‖∑ k : Fin N, entryPair (Yᴴ * Polynomial.aeval A (b k) * Y) (C k)‖^2 ≤
        (a / γ^2) * ∑ k : Fin N, faberWeight k * hsSq (C k)) := by
    have hs := htest N C
    simp only [faber_pairing] at hs
    have hv := cross_boundary_estimate A b h hexpand hlower R hR hcoeff X Y
    have hl := hv (F * faberPolynomial b C)
    have hr := hv (faberPolynomial b C * F)
    rw [hs.1,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hγ,mul_pow] at hl
    rw [hs.2,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hγ,mul_pow] at hr
    have hm := polynomialEnergy_mul_le h hh F (faberPolynomial b C) hF
    have hl' := hl.trans (mul_le_mul_of_nonneg_left (hm.1.trans (hupper N C)) ha)
    have hr' := hr.trans (mul_le_mul_of_nonneg_left (hm.2.trans (hupper N C)) ha)
    constructor
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
      convert hl' using 1 ; ring
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
      convert hr' using 1 ; ring
  constructor
  · exact weighted_sequence_dual (fun k => Xᴴ * Polynomial.aeval A (b k) * X)
      (a / γ^2) hdiv (fun N C => (hbound N C).1)
  · exact weighted_sequence_dual (fun k => Yᴴ * Polynomial.aeval A (b k) * Y)
      (a / γ^2) hdiv (fun N C => (hbound N C).2)

end DirectCrouzeix

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/DomainCore.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem analytic_domain_core {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) (b : ℕ → Polynomial ℂ) (hb0 : b 0 = 1)
    (h : BoundaryCircle → ℂ) (hh : Continuous h)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (hupper : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      polynomialEnergy h (faberPolynomial b C) ≤ ∑ k : Fin N, faberWeight k * hsSq (C k))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (hposfreq : ∀ k : ℤ, 0 < k → fourierCoeff R k = 0)
    (hpositive : ∀ t, (R t + (R t)ᴴ).PosSemidef)
    (F : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (h t) F‖ ≤ 1) :
    ‖tensorPolynomial A F‖ ≤ 2 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let γ := ‖tensorPolynomial A F‖
  by_cases hγ0 : γ = 0
  · change γ ≤ 2
    rw [hγ0]
    norm_num
  have hγ : 0 < γ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hγ0)
  let T := Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F)
  have hT : ‖T‖ = γ := Matrix.l2_opNorm_toEuclideanCLM _
  obtain ⟨x,y,hx,hy,hxy,hyx⟩ := exists_singular_pair T (hT ▸ hγ)
  rw [hT] at hxy hyx
  let X := matrixify x
  let Y := matrixify y
  have hFx : T (hsVector X) = (γ : ℂ) • hsVector Y := by simpa only [X,Y,hsVector_matrixify] using hxy
  have hFy : ContinuousLinearMap.adjoint T (hsVector Y) = (γ : ℂ) • hsVector X := by
    simpa only [X,Y,hsVector_matrixify] using hyx
  let P := fun t => Xᴴ * R t * X
  let Q := fun t => Yᴴ * R t * Y
  let M := fun t => Yᴴ * R t * X
  let L := fun t => Xᴴ * R t * Y
  have hC (U V : Matrix (Fin n) (Fin m) ℂ) :
      Continuous (fun t => Vᴴ * R t * U) := (compressionCLM U V).continuous.comp hR
  have hCp (U V : Matrix (Fin n) (Fin m) ℂ) (k : ℤ) (hk : 0 < k) :
      fourierCoeff (fun t => Vᴴ * R t * U) k = 0 := by
    rw [fourierCoeff_compression U V R hR,hposfreq k hk]
    simp
  have hCc (U V : Matrix (Fin n) (Fin m) ℂ) (k : ℕ) :
      fourierCoeff (fun t => Vᴴ * R t * U) (-(k : ℤ)) = Vᴴ * Polynomial.aeval A (b k) * U := by
    rw [fourierCoeff_compression U V R hR,hcoeff]
  have hC0 (U V : Matrix (Fin n) (Fin m) ℂ) :
      fourierCoeff (fun t => Vᴴ * R t * U) 0 = Vᴴ * U := by
    simpa only [Int.natCast_zero,neg_zero,hb0,map_one,Matrix.mul_one] using hCc U V 0
  let a := ∫ t, hsSq (M t) ∂circleMeasure
  have ha : 0 ≤ a := integral_nonneg (fun _ => hsSq_nonneg _)
  have hapos : 0 < a := by
    have hv := cross_boundary_estimate A b h hexpand hlower R hR hcoeff X Y F
    change ‖inner ℂ (hsVector Y) (T (hsVector X))‖^2 ≤ a * polynomialEnergy h F at hv
    have hyHS : ‖hsVector Y‖ = 1 := by simpa only [Y,hsVector_matrixify] using hy
    rw [hFx,inner_smul_right,inner_self_eq_norm_sq_to_K,hyHS] at hv
    by_contra hnot
    have ha0 : a = 0 := le_antisymm (not_lt.mp hnot) ha
    rw [ha0,zero_mul] at hv
    have hv' : γ^2 ≤ 0 := by simpa using hv
    nlinarith [sq_pos_of_pos hγ]
  have hdiag := singular_diagonal_estimates A b h hh hexpand hlower hupper R hR hcoeff F hF X Y γ hγ hFx hFy
  change (_ ≤ a/γ^2) ∧ (_ ≤ a/γ^2) at hdiag
  have hPE : (∫ t, hsSq (P t + (P t)ᴴ) ∂circleMeasure) ≤ 4*a/γ^2 := by
    rw [anti_diagonal_energy P (hC X X) (hCp X X)]
    · have hc0 := hCc X X 0
      have hcs (k : ℕ) := hCc X X (k+1)
      simp only [Int.natCast_zero,neg_zero,Nat.cast_add,Nat.cast_one] at hc0 hcs
      simp_rw [show P = (fun t => Xᴴ * R t * X) from rfl,hc0,hcs]
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hdiag.1 (by norm_num : (0 : ℝ) ≤ 4)
    · rw [hC0 X X]
      exact Matrix.isHermitian_conjTranspose_mul_self X
  have hQE : (∫ t, hsSq (Q t + (Q t)ᴴ) ∂circleMeasure) ≤ 4*a/γ^2 := by
    rw [anti_diagonal_energy Q (hC Y Y) (hCp Y Y)]
    · have hc0 := hCc Y Y 0
      have hcs (k : ℕ) := hCc Y Y (k+1)
      simp only [Int.natCast_zero,neg_zero,Nat.cast_add,Nat.cast_one] at hc0 hcs
      simp_rw [show Q = (fun t => Yᴴ * R t * Y) from rfl,hc0,hcs]
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hdiag.2 (by norm_num : (0 : ℝ) ≤ 4)
    · rw [hC0 Y Y]
      exact Matrix.isHermitian_conjTranspose_mul_self Y
  have hME : a ≤ ∫ t, hsSq (M t + (L t)ᴴ) ∂circleMeasure := by
    apply anti_cross_energy M L (hC X Y) (hC Y X) (hCp X Y) (hCp Y X)
    rw [hC0 Y X,hC0 X Y]
    simp
  have hEcont (U V U' V' : Matrix (Fin n) (Fin m) ℂ) :
      Continuous (fun t => hsSq (Vᴴ * R t * U + (V'ᴴ * R t * U')ᴴ)) :=
    continuous_hsSq.comp ((hC U V).add (conjugateTransposeCLM.continuous.comp (hC U' V')))
  have hpi := continuous_integrable_compact circleMeasure (hEcont X X X X)
  have hqi := continuous_integrable_compact circleMeasure (hEcont Y Y Y Y)
  have hmi := continuous_integrable_compact circleMeasure (hEcont X Y Y X)
  have hblock : 2 * (∫ t, hsSq (M t + (L t)ᴴ) ∂circleMeasure) ≤
      (∫ t, hsSq (P t + (P t)ᴴ) ∂circleMeasure) +
      ∫ t, hsSq (Q t + (Q t)ᴴ) ∂circleMeasure := by
    rw [← integral_const_mul,← integral_add hpi hqi]
    exact integral_mono (hmi.const_mul 2) (hpi.add hqi)
      (fun t => positive_block_hsSq (positive_compression_blocks (R t) X Y (hpositive t)))
  have hb : 2*a ≤ 8*a/γ^2 := by
    simp only [mul_div_assoc] at hPE hQE ⊢
    linarith
  have hmul := (le_div_iff₀ (sq_pos_of_pos hγ)).mp hb
  change γ ≤ 2
  have hg2 : γ^2 ≤ 4 := by nlinarith [hapos]
  nlinarith

theorem faber_expansion_of_degree {m : ℕ} (hm : 0 < m)
    (b : ℕ → Polynomial ℂ) (hb : ∀ k, (b k).degree = k) (G : MatrixPolynomial m) :
    ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ), G = faberPolynomial b C := by
  classical
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let S : Polynomial.Sequence (Matrix (Fin m) (Fin m) ℂ) :=
    ⟨fun k => scalarMatrixPolynomial (b k),fun k => by
      rw [scalarMatrixPolynomial,Polynomial.degree_map,hb]⟩
  have hunit (k : ℕ) : IsUnit (S k).leadingCoeff := by
    change IsUnit (scalarMatrixPolynomial (b k)).leadingCoeff
    rw [scalarMatrixPolynomial,Polynomial.leadingCoeff_map]
    apply IsUnit.map
    apply isUnit_iff_ne_zero.mpr
    apply Polynomial.leadingCoeff_ne_zero.mpr
    apply Polynomial.degree_ne_bot.mp
    rw [hb]
    exact WithBot.coe_ne_bot
  let N := G.natDegree+1
  have himage : Set.range (fun k : Fin N => S k) = S '' Set.Iio N := by
    ext p
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨k,k.isLt,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k,hk⟩,rfl⟩
  have hG : G ∈ Submodule.span (Matrix (Fin m) (Fin m) ℂ) (Set.range (fun k : Fin N => S k)) := by
    rw [himage,S.span_degreeLT (fun k _ => hunit k),Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt G.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self G.natDegree)
  obtain ⟨C,hC⟩ := (Submodule.mem_span_range_iff_exists_fun (Matrix (Fin m) (Fin m) ℂ)).mp hG
  refine ⟨N,C,?_⟩
  rw [← hC]
  simp only [faberPolynomial,Polynomial.smul_eq_C_mul]
  rfl

end DirectCrouzeix

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

end DirectCrouzeix.Faber

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/CompactIntegrals.lean
section
namespace OAI

universe u_87 u_88 u_89 u_90 u_91 u_92 u_93

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem integrable_of_continuous_compact {α : Type u_87} {E : Type u_88} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem continuousOn_integral_compact {α : Type u_89} {β : Type u_90} {E : Type u_91}
    [MetricSpace α] [ProperSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    [CompactSpace β] [SecondCountableTopology β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure β) [IsFiniteMeasure μ] {s : Set α} (hs : IsOpen s)
    {f : α → β → E} (hf : ContinuousOn f.uncurry (s ×ˢ univ)) :
    ContinuousOn (fun x => ∫ t, f x t ∂μ) s := by
  intro x hx
  obtain ⟨ε,hε,hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hx)
  have hc : Continuous (fun p : closedBall x ε × β => f p.1 p.2) := by
    apply hf.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    intro p
    exact ⟨hsub p.1.property,mem_univ _⟩
  have hi : Continuous (fun y : closedBall x ε => ∫ t, f y t ∂μ) := by
    simpa using continuous_parametric_integral_of_continuous (μ := μ) hc isCompact_univ
  have hi' : ContinuousOn (fun y => ∫ t, f y t ∂μ) (closedBall x ε) :=
    continuousOn_iff_continuous_domRestrict.mpr hi
  exact (hi'.continuousAt (closedBall_mem_nhds x hε)).continuousWithinAt

theorem hasDerivAt_integral_compact {α : Type u_92} {E : Type u_93}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [CompactSpace α] [SecondCountableTopology α]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) [IsFiniteMeasure μ] {s : Set ℂ} (hs : IsOpen s)
    {f f' : ℂ → α → E}
    (hf : ContinuousOn f.uncurry (s ×ˢ univ))
    (hf' : ContinuousOn f'.uncurry (s ×ˢ univ))
    (hd : ∀ z ∈ s, ∀ t, HasDerivAt (fun w => f w t) (f' z t) z)
    {z : ℂ} (hz : z ∈ s) :
    HasDerivAt (fun w => ∫ t, f w t ∂μ) (∫ t, f' z t ∂μ) z := by
  obtain ⟨ε,hε,hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hz)
  have hcf (w : ℂ) (hw : w ∈ s) : Continuous (f w) := by
    exact hf.comp_continuous (continuous_const.prodMk continuous_id) (fun t => ⟨hw,mem_univ _⟩)
  have hcf' (w : ℂ) (hw : w ∈ s) : Continuous (f' w) := by
    exact hf'.comp_continuous (continuous_const.prodMk continuous_id) (fun t => ⟨hw,mem_univ _⟩)
  obtain ⟨B,hB⟩ := ((isCompact_closedBall z ε).prod isCompact_univ).exists_bound_of_continuousOn
    (hf'.mono (prod_mono hsub Subset.rfl))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := closedBall z ε) (bound := fun _ => B) (closedBall_mem_nhds z hε)
    ?_ (integrable_of_continuous_compact μ (hcf z hz))
    (hcf' z hz).aestronglyMeasurable ?_ (integrable_const B) ?_).2
  · filter_upwards [hs.mem_nhds hz] with w hw
    exact (hcf w hw).aestronglyMeasurable
  · exact ae_of_all μ (fun t w hw => hB (w,t) ⟨hw,mem_univ _⟩)
  · exact ae_of_all μ (fun t w hw => hd w (hsub hw) t)

abbrev Parameter := Set.Icc (0 : ℝ) 1

def chord (u v : ℂ) (t : ℝ) : ℂ := (1-t) • u + t • v

theorem chord_mem {s : Set ℂ} (hs : Convex ℝ s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : chord u v t ∈ s :=
  hs hu hv (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel _ _)

theorem continuous_chord : Continuous (fun p : (ℂ × ℂ) × ℝ => chord p.1.1 p.1.2 p.2) := by
  unfold chord
  fun_prop

def chordIntegral (f : ℂ → ℂ) (w : Parameter → ℂ) (u v : ℂ) : ℂ :=
  ∫ t : Parameter, w t * f (chord u v t)

theorem continuousOn_chordIntegral {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : ContinuousOn f s) {w : Parameter → ℂ} (hw : Continuous w) :
    ContinuousOn (fun p : ℂ × ℂ => chordIntegral f w p.1 p.2) (s ×ˢ s) := by
  apply continuousOn_integral_compact volume (hs.prod hs)
  apply (hw.comp continuous_snd).continuousOn.mul
  apply hf.comp
  · exact (continuous_chord.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).continuousOn
  · intro p hp
    exact chord_mem hconv hp.1.1 hp.1.2 p.2.property

theorem hasDerivAt_chord_left (u v : ℂ) (t : ℝ) :
    HasDerivAt (fun z => chord z v t) ((1-t : ℝ) : ℂ) u := by
  simpa [chord] using ((hasDerivAt_id u).const_smul (1-t : ℝ)).add_const (t • v)

theorem hasDerivAt_chord_right (u v : ℂ) (t : ℝ) :
    HasDerivAt (fun z => chord u z t) (t : ℂ) v := by
  simpa [chord] using ((hasDerivAt_id v).const_smul t).const_add ((1-t) • u)

theorem hasDerivAt_chordIntegral_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {w : Parameter → ℂ} (hw : Continuous w)
    {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    HasDerivAt (fun z => chordIntegral f w z v)
      (chordIntegral (deriv f) (fun t => w t * ((1-(t : ℝ) : ℝ) : ℂ)) u v) u := by
  have hc : ContinuousOn (fun p : ℂ × Parameter => chord p.1 v p.2) (s ×ˢ univ) := by
    unfold chord
    fun_prop
  have hm : MapsTo (fun p : ℂ × Parameter => chord p.1 v p.2) (s ×ˢ univ) s :=
    fun p hp => chord_mem hconv hp.1 hv p.2.property
  apply hasDerivAt_integral_compact volume hs
    ((hw.comp continuous_snd).continuousOn.mul (hf.continuousOn.comp hc hm))
    (((hw.comp continuous_snd).continuousOn.mul
      (Complex.continuous_ofReal.comp (continuous_const.sub (continuous_subtype_val.comp continuous_snd))).continuousOn).mul
        (hf.deriv.continuousOn.comp hc hm)) ?_ hu
  intro z hz t
  have hd := ((hf _ (chord_mem hconv hz hv t.property)).differentiableAt.hasDerivAt.comp z
    (hasDerivAt_chord_left z v t)).const_mul (w t)
  simpa only [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using hd

theorem hasDerivAt_chordIntegral_right {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {w : Parameter → ℂ} (hw : Continuous w)
    {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    HasDerivAt (fun z => chordIntegral f w u z)
      (chordIntegral (deriv f) (fun t => w t * ((t : ℝ) : ℂ)) u v) v := by
  have hc : ContinuousOn (fun p : ℂ × Parameter => chord u p.1 p.2) (s ×ˢ univ) := by
    unfold chord
    fun_prop
  have hm : MapsTo (fun p : ℂ × Parameter => chord u p.1 p.2) (s ×ˢ univ) s :=
    fun p hp => chord_mem hconv hu hp.1 p.2.property
  apply hasDerivAt_integral_compact volume hs
    ((hw.comp continuous_snd).continuousOn.mul (hf.continuousOn.comp hc hm))
    (((hw.comp continuous_snd).continuousOn.mul
      (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)).continuousOn).mul
        (hf.deriv.continuousOn.comp hc hm)) ?_ hv
  intro z hz t
  have hd := ((hf _ (chord_mem hconv hu hz t.property)).differentiableAt.hasDerivAt.comp z
    (hasDerivAt_chord_right u z t)).const_mul (w t)
  simpa only [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using hd

theorem chordIntegral_one_eq_interval (f : ℂ → ℂ) (u v : ℂ) :
    chordIntegral f (fun _ => 1) u v = ∫ t in (0:ℝ)..1, f (chord u v t) := by
  simp only [chordIntegral, one_mul]
  rw [show (∫ t : Parameter, f (chord u v t)) = ∫ t in Icc (0:ℝ) 1, f (chord u v t) from
      integral_subtype measurableSet_Icc (fun t : ℝ => f (chord u v t)),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

theorem hasDerivAt_chord_time (u v : ℂ) (t : ℝ) :
    HasDerivAt (chord u v) (v-u) t := by
  have hi : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! (Complex.ofRealCLM.hasDerivAt (x := t))
  have hd := ((hi.const_sub 1).mul_const u).add (hi.mul_const v)
  change HasDerivAt (fun y => chord u v y) (v-u) t
  simpa [chord, Complex.real_smul, sub_eq_add_neg, add_comm] using! hd

theorem chordIntegral_deriv_mul {s : Set ℂ} (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    chordIntegral (deriv f) (fun _ => 1) u v * (v-u) = f v - f u := by
  rw [chordIntegral_one_eq_interval, ← intervalIntegral.integral_mul_const]
  have hc : ContinuousOn (fun t : ℝ => chord u v t) (Icc 0 1) := by unfold chord; fun_prop
  have hm : MapsTo (fun t : ℝ => chord u v t) (Icc 0 1) s := fun t ht => chord_mem hconv hu hv ht
  have hi : IntervalIntegrable (fun t : ℝ => deriv f (chord u v t) * (v-u)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (hf.deriv.continuousOn.comp hc hm).mul_const _
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (f := fun t => f (chord u v t))
    (f' := fun t => deriv f (chord u v t) * (v-u)) (fun t ht => by
      have ht' : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
      simpa only [smul_eq_mul, mul_comm, Function.comp_def] using
        ((hf _ (hm ht')).differentiableAt.hasDerivAt.scomp t (hasDerivAt_chord_time u v t))) hi
  simpa [chord] using ht

theorem chordIntegral_deriv_eq_dslope {s : Set ℂ} (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    chordIntegral (deriv f) (fun _ => 1) u v = dslope f v u := by
  by_cases huv : u = v
  · subst u
    have he (t : ℝ) : chord v v t = v := by
      rw [chord, ← add_smul, sub_add_cancel, one_smul]
    simp [chordIntegral, he, dslope_same]
  · rw [dslope_of_ne f huv, slope, smul_eq_mul]
    simp only [vsub_eq_sub]
    have hm := chordIntegral_deriv_mul hconv hf hu hv
    field_simp
    linear_combination -hm

theorem analyticOnNhd_chordIntegral_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {w : Parameter → ℂ} (hw : Continuous w)
    {v : ℂ} (hv : v ∈ s) : AnalyticOnNhd ℂ (fun u => chordIntegral f w u v) s := by
  apply DifferentiableOn.analyticOnNhd _ hs
  intro u hu
  exact (hasDerivAt_chordIntegral_left hs hconv hf hw hu hv).differentiableAt.differentiableWithinAt

theorem analyticOnNhd_chordIntegral_right {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {w : Parameter → ℂ} (hw : Continuous w)
    {u : ℂ} (hu : u ∈ s) : AnalyticOnNhd ℂ (chordIntegral f w u) s := by
  apply DifferentiableOn.analyticOnNhd _ hs
  intro v hv
  exact (hasDerivAt_chordIntegral_right hs hconv hf hw hu hv).differentiableAt.differentiableWithinAt

end DirectCrouzeix.Faber

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/DividedDifferences.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

def divided (g : ℂ → ℂ) (u v : ℂ) : ℂ := chordIntegral (deriv g) (fun _ => 1) u v

def dividedLeft (g : ℂ → ℂ) (u v : ℂ) : ℂ :=
  chordIntegral (deriv (deriv g)) (fun t => (1-(t:ℝ) : ℝ)) u v

def chordDenominator (c : ℂ) (g : ℂ → ℂ) (u v : ℂ) : ℂ := c-u*v*divided g u v

def correction (c : ℂ) (g : ℂ → ℂ) (u v : ℂ) : ℂ :=
  u*v*(divided g u v+u*dividedLeft g u v) / chordDenominator c g u v

theorem divided_eq_dslope {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    divided g u v = dslope g v u := chordIntegral_deriv_eq_dslope hconv hg hu hv

theorem hasDerivAt_divided_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    HasDerivAt (fun z => divided g z v) (dividedLeft g u v) u := by
  simpa only [divided, dividedLeft, one_mul] using
    hasDerivAt_chordIntegral_left hs hconv hg.deriv (continuous_const (y := (1:ℂ))) hu hv

theorem continuousOn_correction {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c : ℂ}
    (hH : ∀ u ∈ s, ∀ v ∈ s, chordDenominator c g u v ≠ 0) :
    ContinuousOn (fun p : ℂ × ℂ => correction c g p.1 p.2) (s ×ˢ s) := by
  have hD := continuousOn_chordIntegral hs hconv hg.deriv.continuousOn (continuous_const (y := (1:ℂ)))
  have hE := continuousOn_chordIntegral hs hconv hg.deriv.deriv.continuousOn
    (show Continuous (fun t : Parameter => ((1-(t:ℝ) : ℝ):ℂ)) by fun_prop)
  exact ((continuous_fst.mul continuous_snd).continuousOn.mul
    (hD.add (continuous_fst.continuousOn.mul hE))).div
    (continuousOn_const.sub ((continuous_fst.mul continuous_snd).continuousOn.mul hD))
    (fun p hp => hH p.1 hp.1 p.2 hp.2)

theorem analyticOnNhd_correction_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c v : ℂ} (hv : v ∈ s)
    (hH : ∀ u ∈ s, chordDenominator c g u v ≠ 0) :
    AnalyticOnNhd ℂ (fun u => correction c g u v) s := by
  have hD := analyticOnNhd_chordIntegral_left hs hconv hg.deriv (continuous_const (y := (1:ℂ))) hv
  have hE := analyticOnNhd_chordIntegral_left hs hconv hg.deriv.deriv
    (show Continuous (fun t : Parameter => ((1-(t:ℝ) : ℝ):ℂ)) by fun_prop) hv
  intro u hu
  exact (((analyticAt_id.mul analyticAt_const).mul ((hD u hu).add (analyticAt_id.mul (hE u hu)))).div
    (analyticAt_const.sub ((analyticAt_id.mul analyticAt_const).mul (hD u hu))) (hH u hu))

theorem analyticOnNhd_correction_right {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c u : ℂ} (hu : u ∈ s)
    (hH : ∀ v ∈ s, chordDenominator c g u v ≠ 0) :
    AnalyticOnNhd ℂ (correction c g u) s := by
  have hD := analyticOnNhd_chordIntegral_right hs hconv hg.deriv (continuous_const (y := (1:ℂ))) hu
  have hE := analyticOnNhd_chordIntegral_right hs hconv hg.deriv.deriv
    (show Continuous (fun t : Parameter => ((1-(t:ℝ) : ℝ):ℂ)) by fun_prop) hu
  intro v hv
  exact (((analyticAt_const.mul analyticAt_id).mul ((hD v hv).add (analyticAt_const.mul (hE v hv)))).div
    (analyticAt_const.sub ((analyticAt_const.mul analyticAt_id).mul (hD v hv))) (hH v hv))

@[simp] theorem correction_zero_left (c : ℂ) (g : ℂ → ℂ) (v : ℂ) : correction c g 0 v = 0 := by
  simp [correction]

@[simp] theorem correction_zero_right (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : correction c g u 0 = 0 := by
  simp [correction]

def exterior (c : ℂ) (g : ℂ → ℂ) (ζ : ℂ) := c*ζ+g ζ⁻¹

theorem hasDerivAt_exterior {s : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s)
    (c : ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) (hζs : ζ⁻¹ ∈ s) :
    HasDerivAt (exterior c g) (c-ζ⁻¹^2*deriv g ζ⁻¹) ζ := by
  have hd := ((hasDerivAt_id ζ).const_mul c).add
    ((hg ζ⁻¹ hζs).differentiableAt.hasDerivAt.comp ζ (hasDerivAt_inv hζ))
  change HasDerivAt (fun z => exterior c g z) _ ζ
  simpa only [exterior, Function.comp_def, id_eq, mul_one, Pi.add_apply, inv_pow,
    div_eq_mul_inv, sub_eq_add_neg, mul_neg, mul_comm, mul_left_comm] using! hd

theorem chordDenominator_off_diagonal {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) (c : ℂ) {u v : ℂ}
    (hu : u ∈ s) (hv : v ∈ s) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v) :
    chordDenominator c g u v = (exterior c g u⁻¹ - exterior c g v⁻¹) / (u⁻¹-v⁻¹) := by
  rw [chordDenominator, divided_eq_dslope hconv hg hu hv, dslope_of_ne g huv]
  simp only [slope, smul_eq_mul, vsub_eq_sub, exterior, inv_inv]
  field_simp
  ring

theorem chordDenominator_diagonal {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) (c : ℂ) {u : ℂ} (hu : u ∈ s) :
    chordDenominator c g u u = c-u^2*deriv g u := by
  rw [chordDenominator, divided_eq_dslope hconv hg hu hu, dslope_same]
  ring

theorem chordDenominator_ne_zero {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c : ℂ} (hc : c ≠ 0)
    (hinj : InjOn (exterior c g) (Inv.inv ⁻¹' s \ {0}))
    (hd : ∀ ζ, ζ ≠ 0 → ζ⁻¹ ∈ s → deriv (exterior c g) ζ ≠ 0)
    {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) : chordDenominator c g u v ≠ 0 := by
  by_cases hu0 : u = 0
  · simp [chordDenominator, hu0, hc]
  by_cases hv0 : v = 0
  · simp [chordDenominator, hv0, hc]
  by_cases huv : u = v
  · subst v
    rw [chordDenominator_diagonal hconv hg c hu]
    have hder := (hasDerivAt_exterior hg c (inv_ne_zero hu0) (by simpa using hu)).deriv
    have hn := hd u⁻¹ (inv_ne_zero hu0) (by simpa using hu)
    rwa [hder,inv_inv] at hn
  · rw [chordDenominator_off_diagonal hconv hg c hu hv hu0 hv0 huv]
    exact div_ne_zero (sub_ne_zero.mpr (fun he => huv (inv_injective (hinj
      ⟨by simpa using hu, by simpa using hu0⟩ ⟨by simpa using hv, by simpa using hv0⟩ he))))
      (sub_ne_zero.mpr (fun he => huv (inv_injective he)))

theorem divided_fundamental {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    (u-v)*divided g u v = g u-g v := by
  have hh := chordIntegral_deriv_mul hconv hg hu hv
  change divided g u v * (v-u) = _ at hh
  linear_combination -hh

theorem divided_derivative_relation {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    divided g u v + (u-v)*dividedLeft g u v = deriv g u := by
  have hd := ((hasDerivAt_id u).sub_const v).mul (hasDerivAt_divided_left hs hconv hg hu hv)
  have he : (fun z => g z-g v) =ᶠ[𝓝 u] (fun z => (z-v)*divided g z v) := by
    filter_upwards [hs.mem_nhds hu] with z hz
    exact (divided_fundamental hconv hg hz hv).symm
  have hid := (hd.congr_of_eventuallyEq he).unique ((hg u hu).differentiableAt.hasDerivAt.sub_const (g v))
  simpa using hid

theorem correction_identity {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) (c : ℂ) {u v : ℂ}
    (hu : u ∈ s) (hv : v ∈ s) (hv0 : v ≠ 0) (huv : u ≠ v)
    (hH : chordDenominator c g u v ≠ 0) :
    correction c g u v = (c-u^2*deriv g u)/(c+u*(g u-exterior c g v⁻¹)) - (1-u/v)⁻¹ := by
  have hD := divided_fundamental hconv hg hu hv
  have hE := divided_derivative_relation hs hconv hg hu hv
  have huv' : v-u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have he : c+u*(g u-exterior c g v⁻¹) = chordDenominator c g u v * (v-u)/v := by
    simp only [exterior,inv_inv,chordDenominator]
    field_simp
    linear_combination -u*v*hD
  rw [he,correction]
  have hd0 : chordDenominator c g u v * (v-u) / v ≠ 0 := div_ne_zero (mul_ne_zero hH huv') hv0
  field_simp
  simp only [chordDenominator]
  linear_combination -u^2*hE

end DirectCrouzeix.Faber

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/TaylorFourier.lean
section
namespace OAI

universe u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

def taylorCoeff {E : Type u_94} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (k : ℕ) : E := (k.factorial : ℂ)⁻¹ • iteratedDeriv k f 0

@[simp] theorem taylorCoeff_zero {E : Type u_95} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) : taylorCoeff f 0 = f 0 := by simp [taylorCoeff]

theorem taylorCoeff_congr {E : Type u_96} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E} (h : f =ᶠ[𝓝 0] g) (k : ℕ) : taylorCoeff f k = taylorCoeff g k := by
  rw [taylorCoeff,taylorCoeff,h.iteratedDeriv_eq k]

theorem taylorCoeff_add {E : Type u_97} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f g : ℂ → E} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    taylorCoeff (fun z => f z+g z) k = taylorCoeff f k+taylorCoeff g k := by
  simp only [taylorCoeff,iteratedDeriv_fun_add (n := k) hf.contDiffAt hg.contDiffAt,smul_add]

theorem taylorCoeff_sum {E : Type u_98} {ι : Type u_99} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    (I : Finset ι) {f : ι → ℂ → E} (hf : ∀ i ∈ I, AnalyticAt ℂ (f i) 0) (k : ℕ) :
    taylorCoeff (fun z => ∑ i ∈ I, f i z) k = ∑ i ∈ I, taylorCoeff (f i) k := by
  simp only [taylorCoeff, iteratedDeriv_fun_sum (fun i hi => (hf i hi).contDiffAt),Finset.smul_sum]

theorem taylorCoeff_smul_const {E : Type u_100} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (v : E) (k : ℕ) :
    taylorCoeff (fun z => f z • v) k = taylorCoeff f k • v := by
  rw [taylorCoeff,iteratedDeriv_smul_const hf.contDiffAt,taylorCoeff,smul_smul,smul_eq_mul]

@[simp] theorem taylorCoeff_const {E : Type u_101} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) (k : ℕ) : taylorCoeff (fun _ => v) k = if k = 0 then v else 0 := by
  by_cases hk : k = 0
  · subst k; simp
  · simp [taylorCoeff,iteratedDeriv_const,hk]

theorem taylorCoeff_pow_mul {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (j k : ℕ) :
    taylorCoeff (fun u => u^j*f u) k = if j ≤ k then taylorCoeff f (k-j) else 0 := by
  classical
  rw [taylorCoeff,iteratedDeriv_fun_mul (f := fun u : ℂ => u^j) (n := k) (by fun_prop) hf.contDiffAt]
  simp only [iteratedDeriv_fun_pow_zero, Nat.cast_ite, Nat.cast_zero]
  by_cases hjk : j ≤ k
  · rw [Finset.sum_eq_single j]
    · simp only [ite_true,smul_eq_mul,if_pos hjk,taylorCoeff]
      have hfac : (k.factorial : ℂ) = (k.choose j : ℂ) * (j.factorial : ℂ) * ((k-j).factorial : ℂ) := by
        exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjk).symm
      have hkn : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have hjn : ((k-j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
      linear_combination -(iteratedDeriv (k-j) f 0)*hfac
    · intro i hi hij
      simp [hij]
    · exact fun h => (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hjk))).elim
  · rw [if_neg hjk]
    have he : ∑ i ∈ Finset.range (k+1), (k.choose i : ℂ) *
        (if i = j then (j.factorial : ℂ) else 0) * iteratedDeriv (k-i) f 0 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hij : i ≠ j := by have hik := Finset.mem_range.mp hi; omega
      simp [hij]
    rw [he,smul_zero]

theorem taylorCoeff_eq_series {E : Type u_102} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 r) (k : ℕ) : taylorCoeff f k = p.coeff k := by
  have hh := hp.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin k => (1:ℂ))
  simp only [← iteratedDeriv_eq_iteratedFDeriv,Finset.sum_const,Finset.card_univ,
    Fintype.card_perm,Fintype.card_fin] at hh
  change iteratedDeriv k f 0 = k.factorial • p.coeff k at hh
  rw [taylorCoeff,hh,← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  simp [Nat.factorial_ne_zero]

abbrev Angle := AddCircle (1:ℝ)

abbrev angularMeasure : Measure Angle := AddCircle.haarAddCircle

def unitPoint (t : Angle) : ℂ := fourier 1 t

@[simp] theorem unitPoint_norm (t : Angle) : ‖unitPoint t‖ = 1 := by
  simp [unitPoint,fourier_apply,Circle.norm_coe]

theorem unitPoint_continuous : Continuous unitPoint := (fourier 1).continuous

theorem unitPoint_pow (t : Angle) (k : ℕ) : unitPoint t ^ k = fourier (k:ℤ) t := by
  simp only [unitPoint,fourier_apply,one_zsmul,← Circle.coe_pow,
    ← AddCircle.toCircle_nsmul,natCast_zsmul]

theorem integral_character_smul {E : Type u_103} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (a b : ℤ) (v : E) :
    (∫ t : Angle, fourier (-a) t • (fourier b t • v) ∂angularMeasure) = if b = a then v else 0 := by
  rw [show (fun t : Angle => fourier (-a) t • (fourier b t • v)) =
      (fun t => (fourier (-a) t * fourier b t) • v) by funext t; rw [smul_smul],
    integral_smul_const]
  have hh := congrFun (fourierCoeff_fourier (T := (1:ℝ)) b) a
  change (∫ t : Angle, fourier (-a) t * fourier b t ∂angularMeasure) = _ at hh
  rw [hh]
  by_cases hab : b = a
  · subst b; simp
  · simp [Ne.symm hab,hab]

theorem fourierCoeff_of_powerSeries {E : Type u_104} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 r) (hr : 1 < r) (k : ℤ) :
    fourierCoeff (fun t : Angle => f (unitPoint t)) k =
      if 0 ≤ k then taylorCoeff f k.toNat else 0 := by
  have h1 : (1:ℂ) ∈ Metric.eball 0 p.radius := by
    simpa [Metric.mem_eball,edist_dist] using hr.trans_le hp.r_le
  have hs : Summable (fun n => ‖p.coeff n‖) := by
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,one_pow,one_smul] using p.summable_norm_apply h1
  have hp' (t : Angle) : HasSum (fun n : ℕ => fourier n t • p.coeff n) (f (unitPoint t)) := by
    have ht : unitPoint t ∈ Metric.eball 0 r := by
      simpa [Metric.mem_eball,edist_dist] using hr
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,unitPoint_pow,zero_add] using hp.hasSum ht
  have hi := hasSum_integral_of_dominated_convergence
    (μ := angularMeasure) (bound := fun (n : ℕ) (_ : Angle) => ‖p.coeff n‖)
    (F := fun (n : ℕ) (t : Angle) => fourier (-k) t • (fourier n t • p.coeff n))
    (f := fun t => fourier (-k) t • f (unitPoint t))
    (fun n => ((fourier (-k)).continuous.smul ((fourier n).continuous.smul continuous_const)).aestronglyMeasurable)
    (fun n => ae_of_all _ (fun t => by simp [norm_smul,fourier_apply,Circle.norm_coe]))
    (ae_of_all _ (fun _ => hs)) (integrable_const _)
    (ae_of_all _ (fun t => (hp' t).const_smul (fourier (-k) t)))
  simp only [integral_character_smul] at hi
  change HasSum (fun n : ℕ => if (n:ℤ) = k then p.coeff n else 0)
    (fourierCoeff (fun t : Angle => f (unitPoint t)) k) at hi
  rw [← hi.tsum_eq]
  cases k with
  | ofNat k =>
    simp [taylorCoeff_eq_series hp]
  | negSucc k =>
    simp

theorem fourierCoeff_of_analytic {E : Type u_105} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {R : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (k : ℤ) :
    fourierCoeff (fun t : Angle => f (unitPoint t)) k =
      if 0 ≤ k then taylorCoeff f k.toNat else 0 := by
  obtain ⟨ρ,hρ1,hρR⟩ := exists_between hR
  let ρ' : ℝ≥0 := ⟨ρ,by linarith⟩
  have hd : DifferentiableOn ℂ f (closedBall 0 (ρ':ℝ)) :=
    hf.differentiableOn.mono (closedBall_subset_ball hρR)
  have hp := hd.hasFPowerSeriesOnBall (R := ρ') (by change 0 < ρ; linarith)
  apply fourierCoeff_of_powerSeries hp
  exact_mod_cast hρ1

end DirectCrouzeix.Faber

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/FaberPolynomials.lean
section
namespace OAI

universe u_106 u_107

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

def localL (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ := (c+u*g u)⁻¹

def localW (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ := u*localL c g u

def localN (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ := (c-u^2*deriv g u)*localL c g u

def faberBasis (c : ℂ) (g : ℂ → ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (k+1), Polynomial.monomial j
    (taylorCoeff (fun u => localN c g u * localW c g u ^ j) k)

theorem analyticAt_localL {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localL c g) 0 := by
  apply (analyticAt_const.add (analyticAt_id.mul hg)).inv
  simpa using hc

theorem analyticAt_localW {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localW c g) 0 := analyticAt_id.mul (analyticAt_localL hc hg)

theorem analyticAt_localN {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localN c g) 0 :=
  (analyticAt_const.sub ((analyticAt_id.pow 2).mul hg.deriv)).mul (analyticAt_localL hc hg)

@[simp] theorem localL_zero (c : ℂ) (g : ℂ → ℂ) : localL c g 0 = c⁻¹ := by simp [localL]

@[simp] theorem localW_zero (c : ℂ) (g : ℂ → ℂ) : localW c g 0 = 0 := by simp [localW]

@[simp] theorem localN_zero {c : ℂ} (hc : c ≠ 0) (g : ℂ → ℂ) : localN c g 0 = 1 := by
  simp [localN,localL,hc]

theorem faberBasis_coeff (c : ℂ) (g : ℂ → ℂ) (k j : ℕ) :
    (faberBasis c g k).coeff j =
      if j ≤ k then taylorCoeff (fun u => localN c g u * localW c g u^j) k else 0 := by
  classical
  simp [faberBasis,Polynomial.coeff_monomial,Finset.sum_ite_eq']

theorem faberBasis_zero {c : ℂ} (hc : c ≠ 0) (g : ℂ → ℂ) : faberBasis c g 0 = 1 := by
  simp [faberBasis,hc]

theorem faberBasis_top_coeff {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    (faberBasis c g k).coeff k = c⁻¹ ^ k := by
  rw [faberBasis_coeff, if_pos le_rfl]
  have he : (fun u => localN c g u * localW c g u^k) =
      (fun u => u^k*(localN c g u*localL c g u^k)) := by funext u; simp only [localW,mul_pow]; ring
  rw [he,taylorCoeff_pow_mul (f := fun u => localN c g u*localL c g u^k)
    ((analyticAt_localN hc hg).mul ((analyticAt_localL hc hg).pow k))]
  simp [hc]

theorem faberBasis_degree {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    (faberBasis c g k).degree = k := by
  have hn : (faberBasis c g k).coeff k ≠ 0 := by rw [faberBasis_top_coeff hc hg]; exact pow_ne_zero _ (inv_ne_zero hc)
  apply (Polynomial.degree_eq_iff_natDegree_eq (fun h => by simp [h] at hn)).mpr
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ hn
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [faberBasis_coeff,if_neg (by omega)]

theorem faberBasis_eval (c : ℂ) (g : ℂ → ℂ) (k : ℕ) (z : ℂ) :
    (faberBasis c g k).eval z = ∑ j ∈ Finset.range (k+1),
      taylorCoeff (fun u => localN c g u * localW c g u^j) k * z^j := by
  simp [faberBasis,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

def scalarGenerating (c : ℂ) (g : ℂ → ℂ) (z u : ℂ) : ℂ :=
  (c-u^2*deriv g u)/(c+u*(g u-z))

theorem analyticAt_scalarGenerating {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (z : ℂ) : AnalyticAt ℂ (scalarGenerating c g z) 0 := by
  apply (analyticAt_const.sub ((analyticAt_id.pow 2).mul hg.deriv)).div
    (analyticAt_const.add (analyticAt_id.mul (hg.sub analyticAt_const)))
  simpa using hc

theorem scalarGenerating_eq_local {c : ℂ} {g : ℂ → ℂ} {z u : ℂ}
    (hu : c+u*g u ≠ 0) : scalarGenerating c g z u = localN c g u/(1-z*localW c g u) := by
  simp only [scalarGenerating,localN,localW,localL]
  field_simp
  congr 1 ; ring

theorem scalarGenerating_coefficient {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (z : ℂ) (k : ℕ) :
    taylorCoeff (scalarGenerating c g z) k = (faberBasis c g k).eval z := by
  let N := localN c g
  let L := localL c g
  let W := localW c g
  have hN : AnalyticAt ℂ N 0 := analyticAt_localN hc hg
  have hL : AnalyticAt ℂ L 0 := analyticAt_localL hc hg
  have hW : AnalyticAt ℂ W 0 := analyticAt_localW hc hg
  let tail := fun u => N u*z^(k+1)*L u^(k+1)/(1-z*W u)
  have ht : AnalyticAt ℂ tail 0 := by
    apply ((hN.mul analyticAt_const).mul (hL.pow (k+1))).div
      (analyticAt_const.sub (analyticAt_const.mul hW))
    simp [W]
  have hsmall : ∀ᶠ u in 𝓝 (0:ℂ), c+u*g u ≠ 0 ∧ 1-z*W u ≠ 0 := by
    apply Filter.Eventually.and
    · exact (analyticAt_const.add (analyticAt_id.mul hg)).continuousAt.eventually_ne (by simpa using hc)
    · exact (analyticAt_const.sub (analyticAt_const.mul hW)).continuousAt.eventually_ne (by simp [W])
  have he : scalarGenerating c g z =ᶠ[𝓝 0]
      (fun u => (∑ j ∈ Finset.range (k+1), (N u*W u^j)*z^j) + u^(k+1)*tail u) := by
    filter_upwards [hsmall] with u hu
    rw [scalarGenerating_eq_local hu.1]
    have hsum := geom_sum_mul_neg (z*W u) (k+1)
    have hre : ∑ j ∈ Finset.range (k+1), N u * W u^j*z^j =
        N u * ∑ j ∈ Finset.range (k+1), (z*W u)^j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; rw [mul_pow]; ring
    rw [hre]
    change N u / (1-z*W u) = _
    simp only [tail]
    field_simp [hu.2]
    have hw : W u = u*L u := rfl
    rw [hw] at hsum ⊢
    linear_combination -N u*hsum
  have hs : AnalyticAt ℂ (fun u => ∑ j ∈ Finset.range (k+1), N u*W u^j*z^j) 0 :=
    Finset.analyticAt_fun_sum _ (fun j hj => (hN.mul (hW.pow j)).mul analyticAt_const)
  have htail : AnalyticAt ℂ (fun u => u^(k+1)*tail u) 0 := (analyticAt_id.pow (k+1)).mul ht
  rw [taylorCoeff_congr he k,taylorCoeff_add hs htail,taylorCoeff_pow_mul ht,
    if_neg (by omega : ¬k+1 ≤ k),add_zero,taylorCoeff_sum]
  · rw [faberBasis_eval]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [taylorCoeff,iteratedDeriv_mul_const_field,smul_eq_mul]
    ring
  · intro j hj
    exact (hN.mul (hW.pow j)).mul analyticAt_const

theorem taylorCoeff_geometric (z : ℂ) (k : ℕ) :
    taylorCoeff (fun u : ℂ => (1-z*u)⁻¹) k = z^k := by
  have he : (fun u : ℂ => (1-z*u)⁻¹) = scalarGenerating 1 (fun _ => 0) z := by
    funext u
    simp [scalarGenerating,sub_eq_add_neg,mul_comm]
  rw [he,scalarGenerating_coefficient (by norm_num) analyticAt_const,faberBasis_eval]
  have he' (j : ℕ) : (fun u => localN 1 (fun _ => 0) u * localW 1 (fun _ => 0) u^j) =
      (fun u : ℂ => u^j) := by funext u; simp [localN,localW,localL]
  simp_rw [he']
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  simp only [taylorCoeff,iteratedDeriv_fun_pow_zero,smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp [hfac]
  · intro j hj hjk
    simp [Ne.symm hjk]
  · simp

theorem faberBasis_exterior {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    {v : ℂ} (hv : v ∈ ball 0 R) (hv0 : v ≠ 0)
    (hH : ∀ u ∈ ball 0 R, chordDenominator c g u v ≠ 0) (k : ℕ) :
    (faberBasis c g k).eval (exterior c g v⁻¹) = v⁻¹^k +
      taylorCoeff (fun u => correction c g u v) k := by
  have h0 : (0:ℂ) ∈ ball 0 R := mem_ball_self hR
  have hgen := analyticAt_scalarGenerating hc (hg 0 h0) (exterior c g v⁻¹)
  have hcorr := analyticOnNhd_correction_left isOpen_ball (convex_ball 0 R) hg hv hH
  have hgeom : AnalyticAt ℂ (fun u : ℂ => (1-v⁻¹*u)⁻¹) 0 := by
    exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).inv (by simp)
  have he : scalarGenerating c g (exterior c g v⁻¹) =ᶠ[𝓝 0]
      (fun u => (1-v⁻¹*u)⁻¹+correction c g u v) := by
    filter_upwards [isOpen_ball.mem_nhds h0, (isOpen_ne.mem_nhds (Ne.symm hv0))] with u hu huv
    have hh := correction_identity isOpen_ball (convex_ball 0 R) hg c hu hv hv0 huv (hH u hu)
    change correction c g u v = scalarGenerating c g (exterior c g v⁻¹) u - _ at hh
    rw [div_eq_mul_inv,mul_comm] at hh
    linear_combination -hh
  rw [← scalarGenerating_coefficient hc (hg 0 h0),taylorCoeff_congr he,
    taylorCoeff_add hgeom (hcorr 0 h0),taylorCoeff_geometric]

@[simp] theorem unitPoint_neg (t : Angle) : unitPoint (-t) = (unitPoint t)⁻¹ := by
  simp [unitPoint,fourier_apply,AddCircle.toCircle_neg,Circle.coe_inv]

theorem fourierCoeff_comp_neg {E : Type u_106} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Angle → E) (k : ℤ) :
    fourierCoeff (fun t => f (-t)) k = fourierCoeff f (-k) := by
  unfold fourierCoeff
  rw [← integral_neg_eq_self (fun t : Angle => fourier (-k) t • f (-t)) angularMeasure]
  congr 1
  funext t
  simp [fourier_apply,smul_neg,neg_smul]

theorem fourierCoeff_of_antianalytic {E : Type u_107} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {R : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (k : ℤ) :
    fourierCoeff (fun t : Angle => f ((unitPoint t)⁻¹)) k =
      if k ≤ 0 then taylorCoeff f (-k).toNat else 0 := by
  have he : (fun t : Angle => f ((unitPoint t)⁻¹)) = (fun t => (fun s => f (unitPoint s)) (-t)) := by
    funext t; change f ((unitPoint t)⁻¹) = f (unitPoint (-t)); rw [unitPoint_neg]
  rw [he,fourierCoeff_comp_neg (fun t : Angle => f (unitPoint t)) k,fourierCoeff_of_analytic hR hf]
  simp only [neg_nonneg]

end DirectCrouzeix.Faber

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/BoundaryKernel.lean
section
namespace OAI

universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115 u_116

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem continuous_circle_integral {α : Type u_108} {E : Type u_109} [TopologicalSpace α]
    [FirstCountableTopology α] [LocallyCompactSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → Angle → E} (hf : Continuous f.uncurry) :
    Continuous (fun x => ∫ t, f x t ∂angularMeasure) := by
  simpa using continuous_parametric_integral_of_continuous (μ := angularMeasure) hf isCompact_univ

theorem continuous_slice_left {α : Type u_110} {β : Type u_111} {E : Type u_112}
    [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace E] (f : α → β → E) (hf : Continuous f.uncurry) (y : β) :
    Continuous (fun x => f x y) := by
  simpa only [Function.comp_def,Function.uncurry] using! hf.comp (continuous_id.prodMk continuous_const)

theorem continuous_slice_right {α : Type u_113} {β : Type u_114} {E : Type u_115}
    [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace E] (f : α → β → E) (hf : Continuous f.uncurry) (x : α) :
    Continuous (f x) := by
  simpa only [Function.comp_def,Function.uncurry] using! hf.comp (continuous_const.prodMk continuous_id)

theorem fourierCoeff_integral_swap {E : Type u_116} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : Angle → Angle → E)
    (hf : Continuous f.uncurry) (k : ℤ) :
    fourierCoeff (fun s => ∫ t, f t s ∂angularMeasure) k =
      ∫ t, fourierCoeff (f t) k ∂angularMeasure := by
  unfold fourierCoeff
  simp_rw [← integral_smul]
  apply (integral_integral_swap _).symm
  exact integrable_of_continuous_compact _
    (((fourier (-k)).continuous.comp continuous_snd).smul hf)

theorem fourierCoeff_conjugate (f : Angle → ℂ) (k : ℤ) :
    fourierCoeff (fun t => conj (f t)) k = conj (fourierCoeff f (-k)) := by
  unfold fourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp []

def boundary (c : ℂ) (g : ℂ → ℂ) (t : Angle) : ℂ := exterior c g (unitPoint t)

def boundaryCorrection (c : ℂ) (g : ℂ → ℂ) (t s : Angle) : ℂ :=
  correction c g ((unitPoint t)⁻¹) ((unitPoint s)⁻¹)

def boundaryCoefficient (c : ℂ) (g : ℂ → ℂ) (k : ℕ) (s : Angle) : ℂ :=
  fourierCoeff (fun t => boundaryCorrection c g t s) (-(k:ℤ))

def boundaryKernel (c : ℂ) (g : ℂ → ℂ) (t s : Angle) : ℝ :=
  1 + 2*(boundaryCorrection c g t s).re

theorem unitPoint_ne_zero (t : Angle) : unitPoint t ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [unitPoint_norm]; norm_num)

theorem unitPoint_inv_mem {R : ℝ} (hR : 1 < R) (t : Angle) :
    (unitPoint t)⁻¹ ∈ ball (0:ℂ) R := by
  simpa only [mem_ball,dist_zero_right,norm_inv,unitPoint_norm,inv_one] using hR

theorem continuous_boundary {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (c : ℂ) : Continuous (boundary c g) := by
  have hi : Continuous (fun t => (unitPoint t)⁻¹) := unitPoint_continuous.inv₀ unitPoint_ne_zero
  exact (continuous_const.mul unitPoint_continuous).add
    (hg.continuousOn.comp_continuous hi (unitPoint_inv_mem hR))

theorem continuous_boundaryCorrection {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0) :
    Continuous (boundaryCorrection c g).uncurry := by
  have hi : Continuous (fun t => (unitPoint t)⁻¹) := unitPoint_continuous.inv₀ unitPoint_ne_zero
  let f : Angle × Angle → ℂ × ℂ := fun p => ((unitPoint p.1)⁻¹,(unitPoint p.2)⁻¹)
  have hf : Continuous f := (hi.comp continuous_fst).prodMk (hi.comp continuous_snd)
  have hmaps : MapsTo f univ (ball 0 R ×ˢ ball 0 R) :=
    fun p _ => ⟨unitPoint_inv_mem hR p.1,unitPoint_inv_mem hR p.2⟩
  have he : (boundaryCorrection c g).uncurry = (fun p : ℂ × ℂ => correction c g p.1 p.2) ∘ f := rfl
  rw [he]
  exact (continuousOn_correction isOpen_ball (convex_ball 0 R) hg hH).comp_continuous hf
    (fun p => hmaps (mem_univ p))

theorem continuous_boundaryCoefficient {c : ℂ} {g : ℂ → ℂ}
    (hS : Continuous (boundaryCorrection c g).uncurry) (k : ℕ) :
    Continuous (boundaryCoefficient c g k) := by
  have hs : Continuous (fun p : Angle × Angle => boundaryCorrection c g p.2 p.1) := by
    simpa only [Function.uncurry,Function.comp_def] using! hS.comp continuous_swap
  have hf : Continuous (fun p : Angle × Angle => fourier (-(-(k:ℤ))) p.2) :=
    (fourier (-(-(k:ℤ)))).continuous.comp continuous_snd
  have hh := continuous_circle_integral (f := fun s t => fourier (-(-(k:ℤ))) t • boundaryCorrection c g t s)
    (hf.smul hs)
  exact hh

theorem boundaryCorrection_left_coeff {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (s : Angle) (j : ℤ) :
    fourierCoeff (fun t => boundaryCorrection c g t s) j =
      if j ≤ 0 then taylorCoeff (fun u => correction c g u ((unitPoint s)⁻¹)) (-j).toNat else 0 := by
  exact fourierCoeff_of_antianalytic hR
    (analyticOnNhd_correction_left isOpen_ball (convex_ball 0 R) hg (unitPoint_inv_mem hR s)
      (fun u hu => hH u hu _ (unitPoint_inv_mem hR s))) j

theorem boundaryCorrection_right_coeff {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (t : Angle) (j : ℤ) :
    fourierCoeff (boundaryCorrection c g t) j =
      if j ≤ 0 then taylorCoeff (correction c g ((unitPoint t)⁻¹)) (-j).toNat else 0 := by
  exact fourierCoeff_of_antianalytic hR
    (analyticOnNhd_correction_right isOpen_ball (convex_ball 0 R) hg (unitPoint_inv_mem hR t)
      (fun v hv => hH _ (unitPoint_inv_mem hR t) v hv)) j

theorem boundaryCoefficient_eq_taylor {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (k : ℕ) (s : Angle) :
    boundaryCoefficient c g k s = taylorCoeff (fun u => correction c g u ((unitPoint s)⁻¹)) k := by
  simp [boundaryCoefficient,boundaryCorrection_left_coeff hR hg hH]

theorem boundaryCoefficient_zero {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0) (s : Angle) :
    boundaryCoefficient c g 0 s = 0 := by
  rw [boundaryCoefficient_eq_taylor hR hg hH]; simp

theorem faberBasis_boundary {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (k : ℕ) (s : Angle) :
    (faberBasis c g k).eval (boundary c g s) = fourier (k:ℤ) s + boundaryCoefficient c g k s := by
  rw [boundaryCoefficient_eq_taylor hR hg hH]
  have he := faberBasis_exterior (by linarith : 0 < R) hg hc (unitPoint_inv_mem hR s)
    (inv_ne_zero (unitPoint_ne_zero s)) (fun u hu => hH u hu _ (unitPoint_inv_mem hR s)) k
  simpa only [inv_inv,unitPoint_pow,boundary] using he

theorem boundaryCoefficient_no_nonnegative {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (k : ℕ) (j : ℤ) (hj : 0 ≤ j) :
    fourierCoeff (boundaryCoefficient c g k) j = 0 := by
  have hS := continuous_boundaryCorrection hR hg hH
  have hcont : Continuous (fun p : Angle × Angle => fourier (k:ℤ) p.1 * boundaryCorrection c g p.1 p.2) :=
    ((fourier (k:ℤ)).continuous.comp continuous_fst).mul hS
  change fourierCoeff (fun s => ∫ t, fourier (-(-(k:ℤ))) t • boundaryCorrection c g t s ∂angularMeasure) j = 0
  simp only [neg_neg,smul_eq_mul]
  rw [fourierCoeff_integral_swap (fun t s => fourier (k:ℤ) t * boundaryCorrection c g t s) hcont]
  have hr (t : Angle) : fourierCoeff (boundaryCorrection c g t) j = 0 := by
    rw [boundaryCorrection_right_coeff hR hg hH]
    by_cases hj0 : j = 0
    · subst j; simp
    · rw [if_neg (by omega)]
  have he (t : Angle) : fourierCoeff (fun s => fourier (k:ℤ) t * boundaryCorrection c g t s) j = 0 := by
    simp only [fourierCoeff,smul_eq_mul]
    rw [show (fun s => fourier (-j) s * (fourier (k:ℤ) t * boundaryCorrection c g t s)) =
      (fun s => fourier (k:ℤ) t * (fourier (-j) s * boundaryCorrection c g t s)) by funext s; ring,
      integral_const_mul]
    change fourier (k:ℤ) t * fourierCoeff (boundaryCorrection c g t) j = 0
    rw [hr,mul_zero]
  simp only [he,integral_zero]

theorem continuous_boundaryKernel {c : ℂ} {g : ℂ → ℂ}
    (hS : Continuous (boundaryCorrection c g).uncurry) : Continuous (boundaryKernel c g).uncurry := by
  exact continuous_const.add (continuous_const.mul (Complex.continuous_re.comp hS))

theorem boundaryCorrection_marginals {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0) :
    (∀ s, ∫ t, boundaryCorrection c g t s ∂angularMeasure = 0) ∧
      (∀ t, ∫ s, boundaryCorrection c g t s ∂angularMeasure = 0) := by
  constructor
  · intro s
    have he := boundaryCorrection_left_coeff hR hg hH s 0
    simpa [fourierCoeff] using he
  · intro t
    have he := boundaryCorrection_right_coeff hR hg hH t 0
    simpa [fourierCoeff] using he

theorem boundaryKernel_marginals {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0) :
    (∀ s, ∫ t, boundaryKernel c g t s ∂angularMeasure = 1) ∧
      (∀ t, ∫ s, boundaryKernel c g t s ∂angularMeasure = 1) := by
  have hS := continuous_boundaryCorrection hR hg hH
  have hm := boundaryCorrection_marginals hR hg hH
  have hint (f : Angle → ℂ) (hf : Continuous f) (hz : ∫ t, f t ∂angularMeasure = 0) :
      (∫ t, (1 + 2*(f t).re) ∂angularMeasure) = 1 := by
    have hfi := integrable_of_continuous_compact angularMeasure hf
    change (∫ t, (1 + 2*RCLike.re (f t)) ∂angularMeasure) = 1
    rw [integral_add (integrable_const 1) (hfi.re.const_mul 2),integral_const_mul,
      integral_re hfi,hz]
    simp
  constructor
  · intro s
    change (∫ t, 1+2*(boundaryCorrection c g t s).re ∂angularMeasure) = 1
    exact hint (fun t => boundaryCorrection c g t s) (continuous_slice_left _ hS s) (hm.1 s)
  · intro t
    change (∫ s, 1+2*(boundaryCorrection c g t s).re ∂angularMeasure) = 1
    exact hint (boundaryCorrection c g t) (continuous_slice_right _ hS t) (hm.2 t)

theorem boundaryKernel_complex (c : ℂ) (g : ℂ → ℂ) (t s : Angle) :
    (boundaryKernel c g t s : ℂ) = 1+boundaryCorrection c g t s+conj (boundaryCorrection c g t s) := by
  apply Complex.ext <;> simp [boundaryKernel] ; ring

theorem boundaryKernel_character {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (k : ℕ) (hk : k ≠ 0) (s : Angle) :
    (∫ t, (boundaryKernel c g t s : ℂ) * fourier (k:ℤ) t ∂angularMeasure) =
      boundaryCoefficient c g k s := by
  have hS : Continuous (fun t => boundaryCorrection c g t s) :=
    continuous_slice_left _ (continuous_boundaryCorrection hR hg hH) s
  have hf := (fourier (T := (1:ℝ)) (k:ℤ)).continuous
  have h1 : (∫ t : Angle, fourier (k:ℤ) t ∂angularMeasure) = 0 := by
    have he := integral_character_smul 0 (k:ℤ) (1:ℂ)
    simpa [hk] using he
  have h2 : (∫ t, boundaryCorrection c g t s * fourier (k:ℤ) t ∂angularMeasure) =
      boundaryCoefficient c g k s := by
    simp only [boundaryCoefficient,fourierCoeff,neg_neg,smul_eq_mul]
    congr 1; funext t; ring
  have h3 : (∫ t, conj (boundaryCorrection c g t s) * fourier (k:ℤ) t ∂angularMeasure) = 0 := by
    have he := fourierCoeff_conjugate (fun t => boundaryCorrection c g t s) (-(k:ℤ))
    rw [neg_neg,boundaryCorrection_left_coeff hR hg hH,if_neg (by omega)] at he
    simpa only [fourierCoeff,neg_neg,smul_eq_mul,mul_comm,map_zero] using he
  have hi1 : Integrable (fun t : Angle => fourier (k:ℤ) t) angularMeasure := integrable_of_continuous_compact _ hf
  have hi2 : Integrable (fun t : Angle => boundaryCorrection c g t s * fourier (k:ℤ) t) angularMeasure :=
    integrable_of_continuous_compact _ (hS.mul hf)
  have hi3 : Integrable (fun t : Angle => conj (boundaryCorrection c g t s) * fourier (k:ℤ) t) angularMeasure := by
    simpa only [starRingEnd_apply] using! integrable_of_continuous_compact angularMeasure (hS.star.mul hf)
  have ha := integral_add (hi1.add hi2) hi3
  have hb := integral_add hi1 hi2
  simp only [Pi.add_apply] at ha hb
  simp_rw [boundaryKernel_complex,add_mul,one_mul]
  rw [ha,hb,h1,h2,h3,zero_add,add_zero]

end DirectCrouzeix.Faber

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/KernelContraction.lean
section
namespace OAI

universe u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem weighted_integral_norm_sq_le {α : Type u_117} {E : Type u_118} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (k : α → ℝ) (u : α → E)
    (hk : ∀ x, 0 ≤ k x) (hki : Integrable k μ)
    (hui : Integrable (fun x => k x • u x) μ)
    (hsqi : Integrable (fun x => k x * ‖u x‖ ^ 2) μ)
    (hmass : ∫ x, k x ∂μ = 1) :
    ‖∫ x, k x • u x ∂μ‖ ^ 2 ≤ ∫ x, k x * ‖u x‖ ^ 2 ∂μ := by
  let v := ∫ x, k x • u x ∂μ
  have hii : Integrable (fun x => inner ℝ v (k x • u x)) μ :=
    (innerSL ℝ v).integrable_comp hui
  have hi : (∫ x, inner ℝ v (k x • u x) ∂μ) = ‖v‖ ^ 2 := by
    change (∫ x, (innerSL ℝ v) (k x • u x) ∂μ) = _
    rw [(innerSL ℝ v).integral_comp_comm hui]
    exact real_inner_self_eq_norm_sq v
  have hn : 0 ≤ ∫ x, k x * ‖u x - v‖ ^ 2 ∂μ :=
    integral_nonneg (fun x => mul_nonneg (hk x) (sq_nonneg _))
  have hexp : (fun x => k x * ‖u x - v‖ ^ 2) =
      fun x => (k x * ‖u x‖ ^ 2 - 2 * inner ℝ v (k x • u x)) + k x * ‖v‖ ^ 2 := by
    funext x
    rw [norm_sub_sq_real, inner_smul_right, real_inner_comm v (u x)]
    ring
  rw [hexp] at hn
  have hsubi : Integrable (fun x => k x * ‖u x‖ ^ 2 - 2 * inner ℝ v (k x • u x)) μ :=
    hsqi.sub (hii.const_mul 2)
  have hconsti : Integrable (fun x => k x * ‖v‖ ^ 2) μ := hki.mul_const _
  rw [integral_add hsubi hconsti, integral_sub hsqi (hii.const_mul 2),
    integral_const_mul, integral_mul_const, hi, hmass] at hn
  change ‖v‖ ^ 2 ≤ _
  linarith

theorem continuous_integrable_compact {α : Type u_119} {E : Type u_120} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem continuous_integral_compact {α : Type u_121} {β : Type u_122} {E : Type u_123}
    [TopologicalSpace α] [FirstCountableTopology α] [LocallyCompactSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    [CompactSpace β] [SecondCountableTopology β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure β) [IsFiniteMeasure μ] {f : α → β → E}
    (hf : Continuous f.uncurry) : Continuous (fun x => ∫ y, f x y ∂μ) := by
  simpa using continuous_parametric_integral_of_continuous (μ := μ) hf isCompact_univ

theorem markov_kernel_contraction {α : Type u_124} {β : Type u_125} {E : Type u_126}
    [MetricSpace α] [MeasurableSpace α] [BorelSpace α] [CompactSpace α]
    [SecondCountableTopology α]
    [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [CompactSpace β]
    [SecondCountableTopology β]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (K : α → β → ℝ) (u : α → E)
    (hK : Continuous K.uncurry) (hu : Continuous u)
    (hpos : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∫ x, K x y ∂μ = 1)
    (hrow : ∀ x, ∫ y, K x y ∂ν = 1) :
    (∫ y, ‖∫ x, K x y • u x ∂μ‖ ^ 2 ∂ν) ≤ ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hKcol (y : β) : Continuous (fun x => K x y) :=
    hK.comp (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun y => ∫ x, K x y • u x ∂μ) := by
    apply continuous_integral_compact
    exact (hK.comp continuous_swap).smul (hu.comp continuous_snd)
  have hs : Integrable (fun p : α × β => K p.1 p.2 * ‖u p.1‖ ^ 2) (μ.prod ν) :=
    continuous_integrable_compact _ (hK.mul ((hu.comp continuous_fst).norm.pow 2))
  calc
    _ ≤ ∫ y, ∫ x, K x y * ‖u x‖ ^ 2 ∂μ ∂ν := by
      apply integral_mono (continuous_integrable_compact _ (hT.norm.pow 2))
        hs.integral_prod_right
      intro y
      exact weighted_integral_norm_sq_le μ (fun x => K x y) u (fun x => hpos x y)
        (continuous_integrable_compact _ (hKcol y))
        (continuous_integrable_compact _ ((hKcol y).smul hu))
        (continuous_integrable_compact _ ((hKcol y).mul (hu.norm.pow 2))) (hcol y)
    _ = ∫ x, ∫ y, K x y * ‖u x‖ ^ 2 ∂ν ∂μ := (integral_integral_swap hs).symm
    _ = _ := by simp_rw [integral_mul_const, hrow, one_mul]

section Hilbert

variable {E : Type u_127} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def positiveSeries {N : ℕ} (C : Fin N → E) (t : Angle) : E :=
  ∑ k : Fin N, fourier (k:ℤ) t • C k

theorem continuous_positiveSeries {E : Type u_127} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {N : ℕ} (C : Fin N → E) :
    Continuous (positiveSeries C) := by
  exact continuous_finsetSum _ (fun k _ => (fourier (k:ℤ)).continuous.smul continuous_const)

theorem fourierCoeff_finite_smul {N : ℕ} (f : Fin N → Angle → ℂ)
    (hf : ∀ k, Continuous (f k)) (C : Fin N → E) (j : ℤ) :
    fourierCoeff (fun t => ∑ k, f k t • C k) j = ∑ k, fourierCoeff (f k) j • C k := by
  unfold fourierCoeff
  simp_rw [Finset.smul_sum,smul_smul]
  rw [integral_finsetSum]
  · simp_rw [integral_smul_const,smul_eq_mul]
  · intro k hk
    exact integrable_of_continuous_compact _ (((fourier (-j)).continuous.mul (hf k)).smul continuous_const)

theorem fourierCoeff_positiveSeries {N : ℕ} (C : Fin N → E) (j : Fin N) :
    fourierCoeff (positiveSeries C) (j:ℤ) = C j := by
  classical
  unfold positiveSeries
  rw [fourierCoeff_finite_smul _ (fun k => (fourier (k:ℤ)).continuous)]
  simp_rw [fourierCoeff_fourier]
  simp only [Pi.single_apply,ite_smul,one_smul,zero_smul]
  have hinj (k : Fin N) : (j:ℤ) = (k:ℤ) ↔ j = k := by
    constructor
    · intro h; apply Fin.ext; exact_mod_cast h
    · intro h; rw [h]
  simp_rw [hinj]
  simp

theorem integral_inner_positiveSeries {N : ℕ} (C : Fin N → E)
    (f : Angle → E) (hf : Continuous f) :
    (∫ t, inner ℂ (positiveSeries C t) (f t) ∂angularMeasure) =
      ∑ k, inner ℂ (C k) (fourierCoeff f (k:ℤ)) := by
  simp only [positiveSeries,sum_inner,inner_smul_left,← fourier_neg]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    have he : (fun t => fourier (-(k:ℤ)) t * inner ℂ (C k) (f t)) =
        (fun t => inner ℂ (C k) (fourier (-(k:ℤ)) t • f t)) := by
      funext t; simp only [inner_smul_right]
    rw [he,integral_inner]
    · rfl
    · exact integrable_of_continuous_compact _ ((fourier (-(k:ℤ))).continuous.smul hf)
  · intro k hk
    exact integrable_of_continuous_compact _
      ((fourier (-(k:ℤ))).continuous.mul (continuous_const.inner hf))

theorem energy_positiveSeries {N : ℕ} (C : Fin N → E) :
    (∫ t, ‖positiveSeries C t‖^2 ∂angularMeasure) = ∑ k, ‖C k‖^2 := by
  have hp := continuous_positiveSeries C
  have he (t : Angle) : ‖positiveSeries C t‖^2 = RCLike.re (inner ℂ (positiveSeries C t) (positiveSeries C t)) := by
    simp [inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow]
  simp_rw [he]
  rw [integral_re (integrable_of_continuous_compact _ (hp.inner hp)),integral_inner_positiveSeries C _ hp]
  simp only [fourierCoeff_positiveSeries,inner_self_eq_norm_sq_to_K,map_sum]
  change (∑ k, ((‖C k‖ : ℂ)^2).re) = ∑ k, ‖C k‖^2
  simp [← Complex.ofReal_pow]

theorem energy_orthogonal_positiveSeries {N : ℕ} (C : Fin N → E)
    (r : Angle → E) (hr : Continuous r) (hfreq : ∀ j : ℤ, 0 ≤ j → fourierCoeff r j = 0) :
    (∫ t, ‖positiveSeries C t+r t‖^2 ∂angularMeasure) =
      (∑ k, ‖C k‖^2) + ∫ t, ‖r t‖^2 ∂angularMeasure := by
  have hp := continuous_positiveSeries C
  have hci : Integrable (fun t => inner ℂ (positiveSeries C t) (r t)) angularMeasure :=
    integrable_of_continuous_compact _ (hp.inner hr)
  have hcross : (∫ t, inner ℂ (positiveSeries C t) (r t) ∂angularMeasure) = 0 := by
    rw [integral_inner_positiveSeries C r hr]
    apply Finset.sum_eq_zero
    intro k hk
    rw [hfreq (k:ℤ) (by positivity),inner_zero_right]
  have hcrossRe : (∫ t, RCLike.re (inner ℂ (positiveSeries C t) (r t)) ∂angularMeasure) = 0 := by
    rw [integral_re hci,hcross]
    rfl
  have hpi : Integrable (fun t => ‖positiveSeries C t‖^2) angularMeasure :=
    integrable_of_continuous_compact _ (hp.norm.pow 2)
  have hri : Integrable (fun t => ‖r t‖^2) angularMeasure := integrable_of_continuous_compact _ (hr.norm.pow 2)
  have hcii : Integrable (fun t => 2*RCLike.re (inner ℂ (positiveSeries C t) (r t))) angularMeasure :=
    hci.re.const_mul 2
  simp_rw [norm_add_sq (𝕜 := ℂ)]
  have ha := integral_add (hpi.add hcii) hri
  have hb := integral_add hpi hcii
  simp only [Pi.add_apply] at ha hb
  rw [ha,hb,integral_const_mul,hcrossRe,mul_zero,add_zero,energy_positiveSeries]

end Hilbert

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FaberHilbert

end DirectCrouzeix.Faber

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/FaberEnergy.lean
section
namespace OAI

universe u_128 u_129

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def faberBoundarySeries {N : ℕ} (c : ℂ) (g : ℂ → ℂ) (C : Fin N → E) (t : Angle) : E :=
  ∑ k : Fin N, (faberBasis c g k).eval (boundary c g t) • C k

def boundaryRemainder {N : ℕ} (c : ℂ) (g : ℂ → ℂ) (C : Fin N → E) (t : Angle) : E :=
  ∑ k : Fin N, boundaryCoefficient c g k t • C k

def nonconstantCoefficients {N : ℕ} (C : Fin N → E) (k : Fin N) : E :=
  if (k:ℕ) = 0 then 0 else C k

theorem continuous_boundaryRemainder {E : Type u_128} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {N : ℕ} (c : ℂ) (g : ℂ → ℂ) (C : Fin N → E)
    (hS : Continuous (boundaryCorrection c g).uncurry) : Continuous (boundaryRemainder c g C) := by
  exact continuous_finsetSum _ (fun k _ => (continuous_boundaryCoefficient hS k).smul continuous_const)

theorem faberBoundarySeries_decomp {E : Type u_128} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    {N : ℕ} (C : Fin N → E) (t : Angle) :
    faberBoundarySeries c g C t = positiveSeries C t + boundaryRemainder c g C t := by
  simp only [faberBoundarySeries,faberBasis_boundary hR hg hc hH,add_smul,
    Finset.sum_add_distrib,positiveSeries,boundaryRemainder]

theorem boundaryRemainder_no_nonnegative {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    {N : ℕ} (C : Fin N → E) (j : ℤ) (hj : 0 ≤ j) :
    fourierCoeff (boundaryRemainder c g C) j = 0 := by
  have hS := continuous_boundaryCorrection hR hg hH
  unfold boundaryRemainder
  rw [fourierCoeff_finite_smul _ (fun k => continuous_boundaryCoefficient hS k)]
  simp only [boundaryCoefficient_no_nonnegative hR hg hH _ j hj,zero_smul,Finset.sum_const_zero]

theorem boundaryKernel_action {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    {N : ℕ} (C : Fin N → E) (s : Angle) :
    (∫ t, boundaryKernel c g t s • positiveSeries (nonconstantCoefficients C) t ∂angularMeasure) =
      boundaryRemainder c g C s := by
  have hK := continuous_slice_left _ (continuous_boundaryKernel (continuous_boundaryCorrection hR hg hH)) s
  simp only [positiveSeries,Finset.smul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : (k:ℕ) = 0
    · simp [nonconstantCoefficients,hk0,boundaryCoefficient_zero hR hg hH]
    · simp only [nonconstantCoefficients,if_neg hk0]
      rw [show (fun t => boundaryKernel c g t s • (fourier (k:ℤ) t • C k)) =
        (fun t => ((boundaryKernel c g t s : ℂ)*fourier (k:ℤ) t) • C k) by
          funext t; rw [← smul_assoc,Complex.real_smul], integral_smul_const,
        boundaryKernel_character hR hg hH k hk0 s]
  · intro k hk
    exact integrable_of_continuous_compact _ (hK.smul ((fourier (k:ℤ)).continuous.smul continuous_const))

theorem faber_hilbert_coefficient_bounds {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (hpositive : ∀ t s, 0 ≤ boundaryKernel c g t s)
    {N : ℕ} (C : Fin N → E) :
    (∑ k, ‖C k‖^2 ≤ ∫ t, ‖faberBoundarySeries c g C t‖^2 ∂angularMeasure) ∧
      ((∫ t, ‖faberBoundarySeries c g C t‖^2 ∂angularMeasure) ≤
        ∑ k : Fin N, (if (k:ℕ) = 0 then 1 else 2)*‖C k‖^2) := by
  have hS := continuous_boundaryCorrection hR hg hH
  have hr := continuous_boundaryRemainder c g C hS
  have he : (∫ t, ‖faberBoundarySeries c g C t‖^2 ∂angularMeasure) =
      (∑ k, ‖C k‖^2) + ∫ t, ‖boundaryRemainder c g C t‖^2 ∂angularMeasure := by
    simp_rw [faberBoundarySeries_decomp hR hg hc hH]
    exact energy_orthogonal_positiveSeries C _ hr (boundaryRemainder_no_nonnegative hR hg hH C)
  have hrnonneg : 0 ≤ ∫ t, ‖boundaryRemainder c g C t‖^2 ∂angularMeasure :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hrbound : (∫ t, ‖boundaryRemainder c g C t‖^2 ∂angularMeasure) ≤
      ∑ k, ‖nonconstantCoefficients C k‖^2 := by
    let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    have hm := boundaryKernel_marginals hR hg hH
    have ht := markov_kernel_contraction angularMeasure angularMeasure (boundaryKernel c g)
      (positiveSeries (nonconstantCoefficients C)) (continuous_boundaryKernel hS)
      (continuous_positiveSeries _) hpositive hm.1 hm.2
    simp_rw [boundaryKernel_action hR hg hH C,energy_positiveSeries] at ht
    exact ht
  have hw : (∑ k, ‖C k‖^2) + ∑ k, ‖nonconstantCoefficients C k‖^2 =
      ∑ k : Fin N, (if (k:ℕ) = 0 then 1 else 2)*‖C k‖^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : (k:ℕ) = 0 <;> simp [nonconstantCoefficients,hk0] ; ring
  constructor
  · rw [he]; linarith
  · rw [he,← hw]; linarith

end FaberHilbert

theorem re_circle_fraction {ζ μ : ℂ} (hζ : ‖ζ‖ = 1) (hμ : ‖μ‖ = 1)
    (hne : ζ ≠ μ) : 2 * (ζ / (ζ - μ)).re = 1 := by
  have hnζ : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using
      (show Complex.normSq ζ = 1 by rw [Complex.normSq_eq_norm_sq, hζ]; norm_num)
  have hnμ : μ.re ^ 2 + μ.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using
      (show Complex.normSq μ = 1 by rw [Complex.normSq_eq_norm_sq, hμ]; norm_num)
  have hd : Complex.normSq (ζ - μ) ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp (sub_ne_zero.mpr hne)
  rw [Complex.div_re]
  field_simp
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at *
  nlinarith

def boundaryNormal (c : ℂ) (g : ℂ → ℂ) (t : Angle) : ℂ :=
  unitPoint t * (c-(unitPoint t)⁻¹^2*deriv g ((unitPoint t)⁻¹))

theorem scalarGenerating_exterior (c : ℂ) (g : ℂ → ℂ) (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    scalarGenerating c g z ζ⁻¹ = ζ*(c-ζ⁻¹^2*deriv g ζ⁻¹)/(exterior c g ζ-z) := by
  unfold scalarGenerating
  have he : c+ζ⁻¹*(g ζ⁻¹-z) = ζ⁻¹*(exterior c g ζ-z) := by
    simp only [exterior]; field_simp; ring
  rw [he,div_mul_eq_div_div,div_inv_eq_mul]
  ring

theorem reciprocal_fraction {ζ μ : ℂ} (hζ : ζ ≠ 0) (hμ : μ ≠ 0) :
    (1-ζ⁻¹/μ⁻¹)⁻¹ = ζ/(ζ-μ) := by
  have hquot : ζ⁻¹/μ⁻¹ = μ/ζ :=
    (div_eq_iff (inv_ne_zero hμ)).2 (by field_simp)
  have he : 1-ζ⁻¹/μ⁻¹ = (ζ-μ)/ζ := by rw [hquot]; field_simp
  rw [he,inv_div]

theorem unitPoint_injective : Function.Injective unitPoint := by
  intro t s h
  apply AddCircle.injective_toCircle (by norm_num : (1:ℝ) ≠ 0)
  apply Subtype.coe_injective
  simpa [unitPoint,fourier_apply] using h

theorem boundaryCorrection_identity {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    {t s : Angle} (hts : t ≠ s) :
    boundaryCorrection c g t s = boundaryNormal c g t/(boundary c g t-boundary c g s) -
      unitPoint t/(unitPoint t-unitPoint s) := by
  have ht := unitPoint_inv_mem hR t
  have hs := unitPoint_inv_mem hR s
  have hn : (unitPoint t)⁻¹ ≠ (unitPoint s)⁻¹ :=
    fun he => hts (unitPoint_injective (inv_injective he))
  have he := correction_identity isOpen_ball (convex_ball 0 R) hg c ht hs
    (inv_ne_zero (unitPoint_ne_zero s)) hn (hH _ ht _ hs)
  change correction c g ((unitPoint t)⁻¹) ((unitPoint s)⁻¹) =
    scalarGenerating c g (exterior c g ((unitPoint s)⁻¹)⁻¹) ((unitPoint t)⁻¹) - _ at he
  rw [inv_inv,scalarGenerating_exterior c g _ (unitPoint_ne_zero t),
    reciprocal_fraction (unitPoint_ne_zero t) (unitPoint_ne_zero s)] at he
  exact he

theorem boundaryKernel_nonneg_off_diagonal {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (hsupport : ∀ t s, 0 ≤ (conj (boundaryNormal c g t)*(boundary c g t-boundary c g s)).re)
    {t s : Angle} (hts : t ≠ s) : 0 ≤ boundaryKernel c g t s := by
  have hfrac := re_circle_fraction (unitPoint_norm t) (unitPoint_norm s)
    (fun he => hts (unitPoint_injective he))
  have hp : 0 ≤ (boundaryNormal c g t/(boundary c g t-boundary c g s)).re := by
    rw [Complex.div_re,← add_div]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simpa [Complex.mul_re] using hsupport t s
  rw [boundaryKernel,boundaryCorrection_identity hR hg hH hts,Complex.sub_re]
  linarith

theorem circle_nonneg_of_off_point (f : Angle → ℝ) (hf : Continuous f) (t : Angle)
    (h : ∀ s, s ≠ t → 0 ≤ f s) : 0 ≤ f t := by
  have hc : Continuous (fun x : ℝ => f (t+(x:Angle))) := hf.comp
    (continuous_const.add (AddCircle.continuous_mk' (1:ℝ)))
  have hlim : Tendsto (fun x : ℝ => f (t+(x:Angle))) (𝓝[>] 0) (𝓝 (f t)) := by
    simpa only [QuotientAddGroup.mk_zero,add_zero] using (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with x hx
  apply h
  intro he
  have hz : (x:Angle) = 0 := by simpa using add_left_cancel (he.trans (add_zero t).symm)
  have hx0 := (AddCircle.coe_eq_zero_iff_of_mem_Ico (show x ∈ Ico (0:ℝ) 1 from ⟨hx.1.le,hx.2⟩)).mp hz
  exact (ne_of_gt hx.1) hx0

theorem boundaryKernel_nonnegative {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (hsupport : ∀ t s, 0 ≤ (conj (boundaryNormal c g t)*(boundary c g t-boundary c g s)).re) :
    ∀ t s, 0 ≤ boundaryKernel c g t s := by
  intro t s
  by_cases hts : t = s
  · subst s
    exact circle_nonneg_of_off_point _
      (continuous_slice_right _ (continuous_boundaryKernel (continuous_boundaryCorrection hR hg hH)) t) t
      (fun s hst => boundaryKernel_nonneg_off_diagonal hR hg hH hsupport (Ne.symm hst))
  · exact boundaryKernel_nonneg_off_diagonal hR hg hH hsupport hts

section BanachAlgebra

variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

end BanachAlgebra

end DirectCrouzeix.Faber

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/FaberCalculus.lean
section
namespace OAI

universe u_129 u_130

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section BanachAlgebra

variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

theorem analyticAt_ringInverse {x : 𝔄} (hx : IsUnit x) :
    AnalyticAt ℂ Ring.inverse x := by
  rcases hx with ⟨u,rfl⟩
  exact analyticAt_inverse u

theorem ringInverse_smul {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄]
    [CompleteSpace 𝔄] {c : ℂ} (hc : c ≠ 0) (x : 𝔄) :
    Ring.inverse (c • x) = c⁻¹ • Ring.inverse x := by
  have hu : IsUnit (algebraMap ℂ 𝔄 c) := (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ 𝔄)
  have hi : Ring.inverse (algebraMap ℂ 𝔄 c) = algebraMap ℂ 𝔄 c⁻¹ := by
    have hm : algebraMap ℂ 𝔄 c * algebraMap ℂ 𝔄 c⁻¹ = 1 := by
      rw [← map_mul,mul_inv_cancel₀ hc,map_one]
    calc
      Ring.inverse (algebraMap ℂ 𝔄 c) = Ring.inverse (algebraMap ℂ 𝔄 c) *
          (algebraMap ℂ 𝔄 c * algebraMap ℂ 𝔄 c⁻¹) := by rw [hm,mul_one]
      _ = algebraMap ℂ 𝔄 c⁻¹ := by rw [← mul_assoc,Ring.inverse_mul_cancel _ hu,one_mul]
  rw [Algebra.smul_def,Ring.inverse_mul (Or.inl hu),hi,Algebra.smul_def,Algebra.commutes]

theorem ringInverse_geometric {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄]
    [CompleteSpace 𝔄] (x : 𝔄) (hx : IsUnit (1-x)) (k : ℕ) :
    Ring.inverse (1-x) = (∑ j ∈ Finset.range (k+1),x^j) + x^(k+1)*Ring.inverse (1-x) := by
  have he := congrArg (fun y : 𝔄 => y * Ring.inverse (1-x)) (geom_sum_mul_neg x (k+1))
  rw [mul_assoc,Ring.mul_inverse_cancel _ hx,mul_one,sub_mul,one_mul] at he
  exact (eq_add_of_sub_eq he.symm)

theorem taylorCoeff_pow_smul_zero {E : Type u_130} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : AnalyticAt ℂ f 0) {j k : ℕ} (hjk : k < j) :
    taylorCoeff (fun u => u^j • f u) k = 0 := by
  have he := iteratedDerivWithin_smul (𝕜 := ℂ) (𝔸 := ℂ) (F := E) (n := k)
    (x := 0) (s := univ) (f := fun u : ℂ => u^j) (g := f)
    (mem_univ _) uniqueDiffOn_univ (by fun_prop) hf.contDiffAt.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at he
  change (k.factorial : ℂ)⁻¹ • iteratedDeriv k ((fun u : ℂ => u^j) • f) 0 = 0
  rw [he]
  have hz : (∑ i ∈ Finset.range (k+1), k.choose i •
      iteratedDeriv i (fun u : ℂ => u^j) 0 • iteratedDeriv (k-i) f 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := by have := Finset.mem_range.mp hi; omega
    simp only [iteratedDeriv_fun_pow_zero,if_neg hij,Nat.cast_zero,smul_zero,zero_smul]
  rw [hz,smul_zero]

def algebraDenominator (c : ℂ) (g : ℂ → ℂ) (A : 𝔄) (u : ℂ) : 𝔄 :=
  (c+u*g u) • 1-u • A

def algebraGenerating (c : ℂ) (g : ℂ → ℂ) (A : 𝔄) (u : ℂ) : 𝔄 :=
  (c-u^2*deriv g u) • Ring.inverse (algebraDenominator c g A u)

theorem analyticAt_algebraDenominator {𝔄 : Type u_129} [NormedRing 𝔄]
    [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] {c : ℂ} {g : ℂ → ℂ} {u : ℂ}
    (hg : AnalyticAt ℂ g u) (A : 𝔄) : AnalyticAt ℂ (algebraDenominator c g A) u := by
  exact ((analyticAt_const.add (analyticAt_id.mul hg)).smul analyticAt_const).sub
    (analyticAt_id.smul analyticAt_const)

theorem analyticAt_algebraGenerating {c : ℂ} {g : ℂ → ℂ} {u : ℂ}
    (hg : AnalyticAt ℂ g u) (A : 𝔄) (hu : IsUnit (algebraDenominator c g A u)) :
    AnalyticAt ℂ (algebraGenerating c g A) u :=
  (analyticAt_const.sub ((analyticAt_id.pow 2).mul hg.deriv)).smul
    ((analyticAt_ringInverse hu).comp (analyticAt_algebraDenominator hg A))

theorem algebraGenerating_local {c : ℂ} {g : ℂ → ℂ} (A : 𝔄) {u : ℂ}
    (h : c+u*g u ≠ 0) :
    algebraGenerating c g A u = localN c g u • Ring.inverse (1-localW c g u • A) := by
  have he : algebraDenominator c g A u = (c+u*g u) • (1-localW c g u • A) := by
    simp only [algebraDenominator,smul_sub,smul_smul,localW,localL]
    congr 1
    congr 1
    field_simp
  rw [algebraGenerating,he,ringInverse_smul h,smul_smul]
  rfl

theorem algebraGenerating_coefficient {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (A : 𝔄) (k : ℕ) :
    taylorCoeff (algebraGenerating c g A) k = Polynomial.aeval A (faberBasis c g k) := by
  classical
  let L := localL c g
  let W := localW c g
  let N := localN c g
  let V := fun u => Ring.inverse (1-W u • A)
  have hL : AnalyticAt ℂ L 0 := analyticAt_localL hc hg
  have hW : AnalyticAt ℂ W 0 := analyticAt_localW hc hg
  have hN : AnalyticAt ℂ N 0 := analyticAt_localN hc hg
  have hd : AnalyticAt ℂ (fun u => (1:𝔄)-W u • A) 0 :=
    analyticAt_const.sub (hW.smul analyticAt_const)
  have hunit : IsUnit ((1:𝔄)-W 0 • A) := by simp [W]
  have hV : AnalyticAt ℂ V 0 := (analyticAt_ringInverse hunit).comp (f := fun u => (1:𝔄)-W u • A) hd
  have hlocal : ∀ᶠ u in 𝓝 0, c+u*g u ≠ 0 :=
    (analyticAt_const.add (analyticAt_id.mul hg)).continuousAt.eventually_ne (by simpa using hc)
  have hu : ∀ᶠ u in 𝓝 0, IsUnit ((1:𝔄)-W u • A) :=
    hd.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hunit)
  let T := fun u => (N u*L u^(k+1)) • (A^(k+1)*V u)
  have hT : AnalyticAt ℂ T 0 := (hN.mul (hL.pow (k+1))).smul (analyticAt_const.mul hV)
  have hs : AnalyticAt ℂ (fun u => ∑ j ∈ Finset.range (k+1), (N u*W u^j) • A^j) 0 :=
    Finset.analyticAt_fun_sum _ (fun j _ => (hN.mul (hW.pow j)).smul analyticAt_const)
  have he : algebraGenerating c g A =ᶠ[𝓝 0]
      (fun u => (∑ j ∈ Finset.range (k+1), (N u*W u^j) • A^j) + u^(k+1) • T u) := by
    filter_upwards [hlocal,hu] with u hlu huu
    rw [algebraGenerating_local A hlu,ringInverse_geometric (W u • A) huu k]
    simp only [smul_add,Finset.smul_sum,smul_pow,smul_smul,smul_mul_assoc]
    congr 1
    change (N u * W u^(k+1)) • (A^(k+1)*V u) =
      u^(k+1) • ((N u*L u^(k+1)) • (A^(k+1)*V u))
    rw [smul_smul]
    congr 1
    change N u * (u*L u)^(k+1) = _
    rw [mul_pow]
    ring
  have htail : AnalyticAt ℂ (fun u => u^(k+1) • T u) 0 := (analyticAt_id.pow (k+1)).smul hT
  rw [taylorCoeff_congr he k,taylorCoeff_add hs htail,
    taylorCoeff_pow_smul_zero hT (by omega : k < k+1),add_zero,taylorCoeff_sum]
  · simp only [faberBasis,map_sum,Polynomial.aeval_monomial,← Algebra.smul_def]
    apply Finset.sum_congr rfl
    intro j hj
    exact taylorCoeff_smul_const (hN.mul (hW.pow j)) (A^j) k
  · exact fun j _ => (hN.mul (hW.pow j)).smul analyticAt_const

theorem algebraGenerating_fourier {R : ℝ} (hR : 1 < R) {c : ℂ} (hc : c ≠ 0)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (ball 0 R)) (A : 𝔄)
    (hunit : ∀ u ∈ closedBall 0 1, IsUnit (algebraDenominator c g A u)) :
    (Continuous (fun t : Angle => algebraGenerating c g A (unitPoint t)⁻¹)) ∧
    (∀ k : ℕ, fourierCoeff (fun t : Angle => algebraGenerating c g A (unitPoint t)⁻¹)
      (-(k:ℤ)) = Polynomial.aeval A (faberBasis c g k)) ∧
    (∀ k : ℤ, 0 < k → fourierCoeff (fun t : Angle => algebraGenerating c g A (unitPoint t)⁻¹) k = 0) := by
  have ha : AnalyticOnNhd ℂ (algebraGenerating c g A) (closedBall 0 1) := by
    intro u hu
    exact analyticAt_algebraGenerating (hg u (closedBall_subset_ball hR hu)) A (hunit u hu)
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_closedBall (0:ℂ) 1).exists_thickening_subset_open
    (isOpen_analyticAt ℂ (algebraGenerating c g A)) ha
  rw [thickening_closedBall hδ (by norm_num : (0:ℝ) ≤ 1)] at hsub
  have hδ1 : 1 < δ+1 := by linarith
  have hsub : AnalyticOnNhd ℂ (algebraGenerating c g A) (ball 0 (δ+1)) := hsub
  have he (k : ℤ) := fourierCoeff_of_antianalytic hδ1 hsub k
  refine ⟨?_,?_,?_⟩
  · exact hsub.continuousOn.comp_continuous (unitPoint_continuous.inv₀ unitPoint_ne_zero)
      (fun t => unitPoint_inv_mem hδ1 t)
  · intro k
    rw [he,if_pos (by omega : -(k:ℤ) ≤ 0)]
    simp only [neg_neg,Int.toNat_natCast]
    exact algebraGenerating_coefficient hc (hg 0 (mem_ball_self (by linarith))) A k
  · intro k hk
    rw [he,if_neg (by omega : ¬k ≤ 0)]

theorem algebraDenominator_exterior {𝔄 : Type u_129} [NormedRing 𝔄]
    [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]
    (c : ℂ) (g : ℂ → ℂ) (A : 𝔄) {u : ℂ} (hu : u ≠ 0) :
    algebraDenominator c g A u = u • (exterior c g u⁻¹ • 1 - A) := by
  simp only [algebraDenominator,exterior,inv_inv,smul_sub,smul_smul]
  congr 1
  congr 1
  field_simp

theorem algebraGenerating_exterior (c : ℂ) (g : ℂ → ℂ) (A : 𝔄) {ζ : ℂ} (hζ : ζ ≠ 0) :
    algebraGenerating c g A ζ⁻¹ = (ζ*(c-ζ⁻¹^2*deriv g ζ⁻¹)) •
      Ring.inverse (exterior c g ζ • 1 - A) := by
  rw [algebraGenerating,algebraDenominator_exterior c g A (inv_ne_zero hζ),inv_inv,
    ringInverse_smul (inv_ne_zero hζ),inv_inv,smul_smul,mul_comm]

end BanachAlgebra

end DirectCrouzeix.Faber

namespace DirectCrouzeix

open MeasureTheory Set Filter Metric

open scoped Topology ComplexConjugate MatrixOrder ComplexOrder

end DirectCrouzeix

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/ExteriorCollar.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix

open MeasureTheory Set Filter Metric

open scoped Topology ComplexConjugate MatrixOrder ComplexOrder

theorem faber_matrix_coefficient_bounds {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, Faber.chordDenominator c g u v ≠ 0)
    (hpositive : ∀ t s, 0 ≤ Faber.boundaryKernel c g t s)
    {m N : ℕ} (C : Fin N → Matrix (Fin m) (Fin m) ℂ) :
    (∑ k, hsSq (C k) ≤ polynomialEnergy (Faber.boundary c g) (faberPolynomial (Faber.faberBasis c g) C))
    ∧
      (polynomialEnergy (Faber.boundary c g) (faberPolynomial (Faber.faberBasis c g) C) ≤
        ∑ k : Fin N, faberWeight k * hsSq (C k)) := by
  have hh := Faber.faber_hilbert_coefficient_bounds hR hg hc hH hpositive (fun k => hsVector (C k))
  have he (t : Faber.Angle) :
      Faber.faberBoundarySeries c g (fun k => hsVector (C k)) t =
        hsVector (matrixPolynomialValue (Faber.boundary c g t) (faberPolynomial (Faber.faberBasis c g) C)) := by
    rw [matrixPolynomialValue_faber]
    ext p
    simp [Faber.faberBoundarySeries,hsVector,Matrix.sum_apply,Matrix.smul_apply]
  simp_rw [he,← hsSq_eq_norm_hsVector_sq] at hh
  exact hh

theorem faber_resolvent_data {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (houtside : ∀ ζ : ℂ, 1 ≤ ‖ζ‖ → Faber.exterior c g ζ ∉ numericalRange A)
    (hsupport : ∀ t, ∀ w ∈ numericalRange A,
      0 ≤ (conj (Faber.boundaryNormal c g t) * (Faber.boundary c g t-w)).re) :
    ∃ Q : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ,
      Continuous Q ∧
      (∀ k : ℕ, fourierCoeff Q (-(k:ℤ)) = Polynomial.aeval A (Faber.faberBasis c g k)) ∧
      (∀ k : ℤ, 0 < k → fourierCoeff Q k = 0) ∧
      (∀ t, (Q t+(Q t)ᴴ).PosSemidef) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Q := fun t : Faber.Angle => Faber.algebraGenerating c g A (Faber.unitPoint t)⁻¹
  have hu : ∀ u ∈ closedBall (0:ℂ) 1, IsUnit (Faber.algebraDenominator c g A u) := by
    intro u hu
    by_cases hu0 : u = 0
    · subst u
      simpa [Faber.algebraDenominator,Algebra.smul_def] using
        (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ))
    · rw [Faber.algebraDenominator_exterior c g A hu0,Algebra.smul_def]
      apply IsUnit.mul ((isUnit_iff_ne_zero.mpr hu0).map (algebraMap ℂ _))
      apply isUnit_resolvent_of_not_mem A
      apply houtside
      rw [norm_inv,one_le_inv₀ (norm_pos_iff.mpr hu0)]
      simpa [mem_closedBall,dist_zero_right] using hu
  have hd := Faber.algebraGenerating_fourier hR hc hg A hu
  refine ⟨Q,hd.1,hd.2.1,hd.2.2,?_⟩
  intro t
  have he : Q t = Faber.boundaryNormal c g t • (Faber.boundary c g t • 1-A)⁻¹ := by
    change Faber.algebraGenerating c g A (Faber.unitPoint t)⁻¹ = _
    rw [Faber.algebraGenerating_exterior c g A (Faber.unitPoint_ne_zero t)]
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  rw [he]
  exact positive_resolvent A _ _ (houtside _ (by rw [Faber.unitPoint_norm])) (hsupport t)

theorem exterior_collar_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hinj : InjOn (Faber.exterior c g) (Inv.inv ⁻¹' ball 0 R \ {0}))
    (hder : ∀ ζ : ℂ, ζ ≠ 0 → ζ⁻¹ ∈ ball 0 R → deriv (Faber.exterior c g) ζ ≠ 0)
    (hboundary : ∀ t s, 0 ≤ (conj (Faber.boundaryNormal c g t) *
      (Faber.boundary c g t-Faber.boundary c g s)).re)
    (houtside : ∀ ζ : ℂ, 1 ≤ ‖ζ‖ → Faber.exterior c g ζ ∉ numericalRange A)
    (hsupport : ∀ t, ∀ w ∈ numericalRange A,
      0 ≤ (conj (Faber.boundaryNormal c g t) * (Faber.boundary c g t-w)).re)
    (F : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (Faber.boundary c g t) F‖ ≤ 1) :
    ‖tensorPolynomial A F‖ ≤ 2 := by
  have hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, Faber.chordDenominator c g u v ≠ 0 :=
    fun _ hu _ hv => Faber.chordDenominator_ne_zero (convex_ball 0 R) hg hc hinj hder hu hv
  have hp := Faber.boundaryKernel_nonnegative hR hg hH hboundary
  have hcs (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ) := faber_matrix_coefficient_bounds hR hg hc hH hp C
  obtain ⟨Q,hQ,hcoeff,hpos,hPSD⟩ := faber_resolvent_data hn A hR hg hc houtside hsupport
  apply analytic_domain_core hn hm A (Faber.faberBasis c g) (Faber.faberBasis_zero hc g)
    (Faber.boundary c g) (Faber.continuous_boundary hR hg c)
    (faber_expansion_of_degree hm _ (Faber.faberBasis_degree hc (hg 0 (mem_ball_self (by linarith)))))
    (fun N C => (hcs N C).1) (fun N C => (hcs N C).2) Q hQ hcoeff hpos hPSD F hF

end DirectCrouzeix

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

end Conformal

end DirectCrouzeix

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/NormalFamilies.lean
section
namespace OAI

universe u_131

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

theorem zero_or_nonvanishing_limit {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hFn : ∀ n z, z ∈ U → F n z ≠ 0)
    (hl : TendstoLocallyUniformlyOn F g atTop U) :
    EqOn g 0 U ∨ ∀ z ∈ U, g z ≠ 0 := by
  have hg : AnalyticOnNhd ℂ g U :=
    (hl.differentiableOn (Eventually.of_forall hF) hU).analyticOnNhd hU
  by_cases hz : EqOn g 0 U
  · exact Or.inl hz
  right
  intro a ha hga
  have hlocal : ¬ ∀ᶠ z in 𝓝 a, g z = 0 := by
    intro he
    exact hz (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc ha he)
  have hp := ((hg a ha).eventually_eq_zero_or_eventually_ne_zero).resolve_left hlocal
  obtain ⟨r, hr, hBU, hBn⟩ : ∃ r > 0, closedBall a r ⊆ U ∧
      ∀ z ∈ closedBall a r, z ≠ a → g z ≠ 0 := by
    simpa only [ofPred_and, subset_inter_iff] using!
      nhds_basis_closedBall.mem_iff.mp ((show ∀ᶠ z in 𝓝 a, z ∈ U from hU.mem_nhds ha).and
        (eventually_nhdsWithin_iff.mp hp))
  have hgR : ContinuousOn (fun z => ‖g z‖) (sphere a r) :=
    hg.continuousOn.norm.mono (sphere_subset_closedBall.trans hBU)
  obtain ⟨b, hb, hmin⟩ := (isCompact_sphere a r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hgR
  have hd : 0 < ‖g b‖ := norm_pos_iff.mpr
    (hBn b (sphere_subset_closedBall hb) (ne_of_mem_sphere hb hr.ne'))
  have hlu : TendstoUniformlyOn F g atTop (sphere a r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hl (sphere a r)
      (sphere_subset_closedBall.trans hBU) (isCompact_sphere a r)
  have hclose : ∀ᶠ n in atTop, ∀ z ∈ sphere a r, dist (F n z) (g z) < ‖g b‖ / 2 :=
    by simpa only [dist_comm] using (Metric.tendstoUniformlyOn_iff.mp hlu) _ (half_pos hd)
  have hlow : ∀ᶠ n in atTop, ‖g b‖ / 2 ≤ ‖F n a‖ := by
    filter_upwards [hclose] with n hn
    have hinv : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (ball a r) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball a hr.ne']
      exact ((hF n).inv (hFn n)).mono hBU
    have hbnd : ∀ z ∈ frontier (ball a r), ‖(F n z)⁻¹‖ ≤ (‖g b‖ / 2)⁻¹ := by
      intro z hz
      rw [frontier_ball a hr.ne'] at hz
      have hlo : ‖g b‖ / 2 ≤ ‖F n z‖ := by
        have ht := norm_sub_norm_le (g z) (F n z)
        rw [← dist_eq_norm, dist_comm] at ht
        have hm : ‖g b‖ ≤ ‖g z‖ := hmin hz
        have hc := hn z hz
        linarith
      rw [norm_inv]
      exact (inv_le_inv₀ (lt_of_lt_of_le (half_pos hd) hlo) (half_pos hd)).mpr hlo
    have hc := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball :
      Bornology.IsBounded (ball a r)) hinv hbnd
      (show a ∈ closure (ball a r) from subset_closure (mem_ball_self hr))
    rw [norm_inv] at hc
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hFn n a ha)) (half_pos hd)).mp hc
  have hcenter : Tendsto (fun n => ‖F n a‖) atTop (𝓝 0) := by
    simpa [hga] using (hl.tendsto_at ha).norm
  have hle := ge_of_tendsto hcenter hlow
  exact (not_le_of_gt (half_pos hd)) hle

theorem constant_or_injective_limit {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hFi : ∀ n, InjOn (F n) U)
    (hl : TendstoLocallyUniformlyOn F g atTop U) :
    (∃ c : ℂ, EqOn g (fun _ => c) U) ∨ InjOn g U := by
  have hg := (hl.differentiableOn (Eventually.of_forall hF) hU).analyticOnNhd hU
  by_cases hc : ∃ c : ℂ, EqOn g (fun _ => c) U
  · exact Or.inl hc
  right
  intro a ha b hb hab
  by_contra hne
  have hV : IsOpen (U \ {a}) := hU.sdiff isClosed_singleton
  have hbV : b ∈ U \ {a} := ⟨hb, by simpa [eq_comm] using hne⟩
  obtain ⟨r, hr, hBr⟩ := Metric.isOpen_iff.mp hV b hbV
  have hBU : ball b r ⊆ U := hBr.trans sdiff_subset
  have hzero : ∀ n z, z ∈ ball b r → F n z - F n a ≠ 0 := by
    intro n z hz he
    have hza := hBr hz
    have heq := hFi n hza.1 ha (sub_eq_zero.mp he)
    exact hza.2 (by simpa using heq)
  have hlc : TendstoLocallyUniformlyOn (fun n z => F n z - F n a)
      (fun z => g z - g a) atTop (ball b r) := by
    exact (hl.sub (hl.tendsto_at ha).tendstoUniformly_const.tendstoLocallyUniformly.tendstoLocallyUniformlyOn).mono hBU
  have hh := zero_or_nonvanishing_limit isOpen_ball (convex_ball b r).isPreconnected
    (fun n => ((hF n).sub_const (F n a)).mono hBU) hzero hlc
  have he : EqOn (fun z => g z - g a) 0 (ball b r) := hh.resolve_right (by
    intro hn
    exact hn b (mem_ball_self hr) (sub_eq_zero.mpr hab.symm))
  have heg : g =ᶠ[𝓝 b] (fun _ => g a) := by
    filter_upwards [ball_mem_nhds b hr] with z hz
    exact sub_eq_zero.mp (he hz)
  exact hc ⟨g a, hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hb heg⟩

def extend (U : Set ℂ) (f : U → ℂ) (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ U then f ⟨z, h⟩ else 0

@[simp] theorem extend_coe {U : Set ℂ} (f : U → ℂ) (z : U) : extend U f z = f z := by
  simp [extend, z.property]

theorem continuousMap_limit {U : Set ℂ} (hU : IsOpen U)
    {F : ℕ → C(U, ℂ)} {g : C(U, ℂ)} (hl : Tendsto F atTop (𝓝 g)) :
    TendstoLocallyUniformlyOn (fun n => extend U (F n)) (extend U g) atTop U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa only [extend_coe, Function.comp_def] using
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hl

theorem bounded_holomorphic_equicontinuous {U : Set ℂ} (hU : IsOpen U)
    {ι : Type u_131} (F : ι → ℂ → ℂ)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hbound : ∀ i z, z ∈ U → ‖F i z‖ ≤ 1) :
    Equicontinuous (fun i (z : U) => F i z) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨R, hR, hBR⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds x.property)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hd (i : ι) (z : ℂ) (hz : z ∈ ball (x : ℂ) r) : ‖deriv (F i) z‖ ≤ 1 / r := by
    have hsub : closedBall z r ⊆ U := by
      intro w hw
      apply hBR
      have ht := dist_triangle w z (x : ℂ)
      have hw' := mem_closedBall.mp hw
      have hz' := mem_ball.mp hz
      change dist w (x : ℂ) ≤ R
      dsimp [r] at hw' hz'
      linarith
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball z hr.ne']
      exact (hF i).mono hsub
    · intro w hw
      exact hbound i w (hsub (sphere_subset_closedBall hw))
  have hbU : ball (x : ℂ) r ⊆ U := by
    intro z hz
    apply hBR
    exact mem_closedBall.mpr ((mem_ball.mp hz).le.trans (by dsimp [r]; linarith))
  refine ⟨min r (ε * r), lt_min hr (mul_pos hε hr), ?_⟩
  intro y hy i
  have hy' : dist (y : ℂ) (x : ℂ) < r := lt_of_lt_of_le hy (min_le_left _ _)
  have hxy : ‖F i y - F i x‖ ≤ (1 / r) * ‖(y : ℂ) - x‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hF i).differentiableAt (hU.mem_nhds (hbU hz)))
      (hd i) (convex_ball (x : ℂ) r) (mem_ball_self hr) hy'
  rw [dist_comm, dist_eq_norm]
  apply lt_of_le_of_lt hxy
  rw [one_div, ← div_eq_inv_mul, div_lt_iff₀ hr]
  rw [← dist_eq_norm]
  exact lt_of_lt_of_le hy (min_le_right _ _)

theorem bounded_holomorphic_compact {U : Set ℂ} (hU : IsOpen U)
    (S : Set C(U, ℂ))
    (hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U ∧ ∀ z : U, ‖f z‖ ≤ 1) :
    IsCompact (closure S) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : T2Space (UniformOnFun U ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      ext x
      simp only [mem_sUnion, mem_ofPred_eq, mem_univ, iff_true]
      exact ⟨{x}, isCompact_singleton, mem_singleton x⟩)
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun f : C(U, ℂ) => (f : U → ℂ)) (𝔖 := {K | IsCompact K})
    (fun _ hK => hK)
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  · intro K hK
    have he := bounded_holomorphic_equicontinuous hU
      (fun f : S => extend U (f : C(U, ℂ)))
      (fun f => (hS f f.property).1)
      (fun f z hz => by simpa [extend, hz] using (hS f f.property).2 ⟨z, hz⟩)
    simpa only [Function.comp_def, extend_coe] using he.equicontinuousOn K
  · intro K hK z hz
    exact ⟨closedBall 0 1, isCompact_closedBall _ _, fun f hf => by
      simpa using (hS f hf).2 z⟩

theorem bounded_holomorphic_closure {U : Set ℂ} (hU : IsOpen U)
    {S : Set C(U, ℂ)}
    (hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U ∧ ∀ z : U, ‖f z‖ ≤ 1)
    {g : C(U, ℂ)} (hg : g ∈ closure S) :
    DifferentiableOn ℂ (extend U g) U ∧ ∀ z : U, ‖g z‖ ≤ 1 := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  obtain ⟨F, hF, hl⟩ := mem_closure_iff_seq_limit.mp hg
  have hl' := continuousMap_limit hU hl
  refine ⟨hl'.differentiableOn (Eventually.of_forall (fun n => (hS _ (hF n)).1)) hU, ?_⟩
  intro z
  have ht := (hl'.tendsto_at z.property).norm
  simpa only [extend_coe] using le_of_tendsto ht
    (Eventually.of_forall (fun n => by simpa only [extend_coe] using (hS _ (hF n)).2 z))

theorem derivative_continuousOn {U : Set ℂ} (hU : IsOpen U)
    {S : Set C(U, ℂ)} (hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U)
    {a : ℂ} (ha : a ∈ U) :
    ContinuousOn (fun f : C(U, ℂ) => deriv (extend U f) a) S := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro F g hl
  have ht : Tendsto (fun n => (F n : C(U, ℂ))) atTop (𝓝 (g : C(U, ℂ))) :=
    continuous_subtype_val.continuousAt.tendsto.comp hl
  have hlu := (continuousMap_limit hU ht).deriv
    (Eventually.of_forall (fun n => hS _ (F n).property)) hU
  exact hlu.tendsto_at ha

theorem strict_bound_of_normalized {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hb : ∀ z ∈ U, ‖f z‖ ≤ 1) {a : ℂ} (ha : a ∈ U) (hfa : f a = 0) :
    MapsTo f U (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff]
  by_contra hn
  have he : ‖f z‖ = 1 := le_antisymm (hb _ hz) (le_of_not_gt hn)
  have hm : IsMaxOn (norm ∘ f) U z := fun w hw => by
    change ‖f w‖ ≤ ‖f z‖
    rw [he]
    exact hb w hw
  have heq := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hUc hU hf hz hm ha
  simp [hfa, he] at heq

open Function Complex

open scoped Pointwise

end Conformal

end DirectCrouzeix

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/ExtremalEmbedding.lean
section
/-
Portions of this file have been adapted from an external source.
The source copyright header and license information are preserved below.
-/


namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

The following conformal embedding declarations are adapted from Mathlib.Analysis.Complex.RiemannMapping.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Complex/RiemannMapping.lean

This code has been modified.
-/

theorem exists_injective_not_dense_image_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, Injective f ∧ ¬Dense (f '' U) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by

  wlog hU₀ : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize this (hUo.vadd (-a)) (by simpa) (by simp [hU])
      (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf_inj, hf_dense, hdf⟩
    refine ⟨f ∘ (-a + ·), hf_inj.comp (add_right_injective (-a)), ?_, fun z hz ↦ ?_⟩
    · simpa only [← image_vadd, Set.image_image] using! hf_dense
    · simpa [Function.comp_def, deriv_comp_const_add] using hdf (-a + z) (mapsTo_image _ _ hz)

  rcases exists_continuousOn_pow_eq hUc hUo continuousOn_id (by rwa [image_id]) two_ne_zero
    with ⟨f, hfc, hf_inv⟩
  replace hf_inv : LeftInverse (· ^ 2) f := hf_inv

  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv z

  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt <| hUo.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf₀ z hz
    · exact .of_forall hf_inv

  refine ⟨f, hf_inv.injective, ?_, fun z hz ↦ ?_⟩
  ·
    simp only [Dense, not_forall, mem_closure_iff_frequently, not_frequently]
    rcases hUc.nonempty with ⟨x, hx⟩

    use -f x

    have : f '' U ∈ 𝓝 (f x) := by
      rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
      exact Filter.image_mem_map <| hUo.mem_nhds hx

    rw [nhds_neg, eventually_neg]

    filter_upwards [this]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    obtain rfl : a = b := by
      rw [← hf_inv b, hab]
      simp [hf_inv a]
    refine hf₀ a ha ?_
    linear_combination hab / 2
  · simpa [(hdf z hz).hasDerivAt.deriv] using hf₀ z hz

lemma exists_mapsTo_unitBall_injOn_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by

  rcases exists_injective_not_dense_image_deriv_ne_zero hUo hUc hU with ⟨f, hf_inj, hfd, hdf⟩

  obtain ⟨x, ε, hε₀, hε⟩ : ∃ (x : ℂ) (ε : ℝ), 0 < ε ∧ ∀ a ∈ U, ε < dist (f a) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hfd
  have hfx : ∀ z ∈ U, f z ≠ x := fun z hz ↦ by simpa using hε₀.trans (hε z hz)

  use fun z ↦ ε / (f z - x)
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · simpa [dist_eq_norm] using hε z hz
    · simpa [sub_eq_zero] using hfx z hz
  case injOn =>
    intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inj.eq_iff] using heq
  case deriv =>
    intro z hz
    have hdz : DifferentiableAt ℂ f z := differentiableAt_of_deriv_ne_zero (hdf z hz)
    rw [(hasDerivAt_const _ _).fun_div (hdz.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [*, ne_of_gt, sub_eq_zero]

structure NormalizedEmbedding (U : Set ℂ) (a : ℂ) (f : ℂ → ℂ) : Prop where
  holomorphic : DifferentiableOn ℂ f U
  disk : MapsTo f U (ball 0 1)
  injective : InjOn f U
  derivative : ∀ z ∈ U, deriv f z ≠ 0
  normalized : f a = 0

theorem exists_normalizedEmbedding {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedEmbedding U a f := by
  obtain ⟨e, hed, hei, he'⟩ :=
    exists_mapsTo_unitBall_injOn_deriv_ne_zero hU hUc hproper
  have he : DifferentiableOn ℂ e U := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (he' z hz)).differentiableWithinAt
  let f : ℂ → ℂ := fun z => (e z - e a) / 2
  have hf' (z : ℂ) (hz : z ∈ U) : HasDerivAt f (deriv e z / 2) z :=
    ((he.hasDerivAt (hU.mem_nhds hz)).sub_const _).div_const _
  refine ⟨f, ⟨he.sub_const _ |>.div_const _, ?_, ?_, ?_, by simp [f]⟩⟩
  · intro z hz
    rw [mem_ball_zero_iff]
    dsimp [f]
    rw [norm_div]
    norm_num
    have h1 := norm_sub_le (e z) (e a)
    have h2 : ‖e z‖ < 1 := mem_ball_zero_iff.mp (hed hz)
    have h3 : ‖e a‖ < 1 := mem_ball_zero_iff.mp (hed ha)
    linarith
  · intro z hz w hw heq
    apply hei hz hw
    dsimp [f] at heq
    exact sub_left_injective ((div_left_inj' (by norm_num : (2 : ℂ) ≠ 0)).mp heq)
  · intro z hz
    rw [(hf' z hz).deriv]
    exact div_ne_zero (he' z hz) (by norm_num)

theorem extend_restrict_eventuallyEq {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} {a : ℂ} (ha : a ∈ U) :
    extend U (fun z : U => f z) =ᶠ[𝓝 a] f := by
  filter_upwards [hU.mem_nhds ha] with z hz
  simp [extend, hz]

theorem exists_extremalEmbedding {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedEmbedding U a f ∧
      ∀ g, NormalizedEmbedding U a g → ‖deriv g a‖ ≤ ‖deriv f a‖ := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let S : Set C(U, ℂ) := {f | NormalizedEmbedding U a (extend U f)}
  have hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U ∧ ∀ z : U, ‖f z‖ ≤ 1 := by
    intro f hf
    refine ⟨hf.holomorphic, fun z => ?_⟩
    simpa only [extend_coe] using (mem_ball_zero_iff.mp (hf.disk z.property)).le
  have hCS := bounded_holomorphic_compact hU S hS
  have hLS (g : C(U, ℂ)) (hg : g ∈ closure S) := bounded_holomorphic_closure hU hS hg
  have hmk (f : ℂ → ℂ) (hf : NormalizedEmbedding U a f) :
      (⟨fun z : U => f z, hf.holomorphic.continuousOn.domRestrict⟩ : C(U, ℂ)) ∈ S := by
    let g : C(U, ℂ) := ⟨fun z : U => f z, hf.holomorphic.continuousOn.domRestrict⟩
    have heq (z : ℂ) (hz : z ∈ U) : extend U g =ᶠ[𝓝 z] f :=
      extend_restrict_eventuallyEq hU hz
    change NormalizedEmbedding U a (extend U g)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact ((hf.holomorphic.differentiableAt (hU.mem_nhds hz)).congr_of_eventuallyEq
        (heq z hz)).differentiableWithinAt
    · intro z hz
      rw [(heq z hz).self_of_nhds]
      exact hf.disk hz
    · intro z hz w hw he
      apply hf.injective hz hw
      rwa [(heq z hz).self_of_nhds, (heq w hw).self_of_nhds] at he
    · intro z hz
      rw [(heq z hz).deriv_eq]
      exact hf.derivative z hz
    · rw [(heq a ha).self_of_nhds]
      exact hf.normalized
  obtain ⟨f₀, hf₀⟩ := exists_normalizedEmbedding hU hUc hproper ha
  let F₀ : C(U, ℂ) := ⟨fun z : U => f₀ z, hf₀.holomorphic.continuousOn.domRestrict⟩
  have hF₀ : F₀ ∈ S := hmk _ hf₀
  obtain ⟨g, hg, hmax⟩ := hCS.exists_isMaxOn ⟨F₀, subset_closure hF₀⟩
    (derivative_continuousOn hU (fun f hf => (hLS _ hf).1) ha).norm
  have hpos : 0 < ‖deriv (extend U g) a‖ :=
    (norm_pos_iff.mpr (hF₀.derivative a ha)).trans_le (hmax (subset_closure hF₀))
  obtain ⟨F, hF, hl⟩ := mem_closure_iff_seq_limit.mp hg
  have hlu := continuousMap_limit hU hl
  have hd := (hLS _ hg).1
  have hn : extend U g a = 0 := by
    exact tendsto_nhds_unique (hlu.tendsto_at ha)
      (by simpa only [(hF _).normalized] using tendsto_const_nhds (x := (0 : ℂ)))
  have hi : InjOn (extend U g) U := by
    apply (constant_or_injective_limit hU hUc.isPathConnected.isConnected.isPreconnected
      (fun n => (hF n).holomorphic) (fun n => (hF n).injective) hlu).resolve_left
    rintro ⟨c, hc⟩
    have he : extend U g =ᶠ[𝓝 a] (fun _ => c) := by
      filter_upwards [hU.mem_nhds ha] with z hz
      exact hc hz
    have hz := he.deriv_eq
    simp only [deriv_const] at hz
    exact (ne_of_gt hpos) (by rw [hz, norm_zero])
  have hder : ∀ z ∈ U, deriv (extend U g) z ≠ 0 := by
    have hdl := hlu.deriv (Eventually.of_forall (fun n => (hF n).holomorphic)) hU
    apply (zero_or_nonvanishing_limit hU hUc.isPathConnected.isConnected.isPreconnected
      (fun n => ((hF n).holomorphic.analyticOnNhd hU).deriv.differentiableOn)
      (fun n => (hF n).derivative) hdl).resolve_left
    intro he
    exact (ne_of_gt hpos) (by rw [he ha, Pi.zero_apply, norm_zero])
  have hgN : NormalizedEmbedding U a (extend U g) :=
    ⟨hd, strict_bound_of_normalized hU hUc.isPathConnected.isConnected.isPreconnected hd
      (fun z hz => by simpa [extend, hz] using (hLS _ hg).2 ⟨z, hz⟩) ha hn, hi, hder, hn⟩
  refine ⟨extend U g, hgN, fun f hf => ?_⟩
  have hm := hmax (subset_closure (hmk f hf))
  change ‖deriv (extend U (fun z : U => f z)) a‖ ≤ _ at hm
  rwa [(extend_restrict_eventuallyEq hU ha).deriv_eq] at hm

end Conformal

end DirectCrouzeix

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/DiskMapping.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

def diskMobius (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)

theorem diskMobius_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  intro he
  have hh := congrArg norm (sub_eq_zero.mp he)
  rw [norm_one, norm_mul, norm_conj] at hh
  have hp := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
  nlinarith

theorem diskMobius_difference (a z : ℂ) :
    ‖1 - conj a * z‖ ^ 2 - ‖z - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im]
  ring

theorem diskMobius_mapsTo {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (diskMobius a) (ball 0 1) (ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  rw [mem_ball_zero_iff, diskMobius, norm_div,
    div_lt_one₀ (norm_pos_iff.mpr (diskMobius_den_ne_zero ha hz'.le))]
  have hd := diskMobius_difference a z
  have hp : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := mul_pos
    (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z])
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - conj a * z)]

theorem diskMobius_hasDerivAt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    HasDerivAt (diskMobius a) ((1 - conj a * a) / (1 - conj a * z) ^ 2) z := by
  have hh := ((hasDerivAt_id z).sub_const a).fun_div
    ((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul (conj a)))
    (diskMobius_den_ne_zero ha hz)
  change HasDerivAt (diskMobius a)
    ((1 * (1 - conj a * z) - (z - a) * (0 - conj a * 1)) / (1 - conj a * z) ^ 2) z at hh
  convert hh using 1
  congr 1
  ring

theorem diskMobius_deriv_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    deriv (diskMobius a) z ≠ 0 := by
  rw [(diskMobius_hasDerivAt ha hz).deriv]
  exact div_ne_zero (diskMobius_den_ne_zero ha ha.le)
    (pow_ne_zero _ (diskMobius_den_ne_zero ha hz))

theorem diskMobius_injOn {a : ℂ} (ha : ‖a‖ < 1) :
    InjOn (diskMobius a) (ball 0 1) := by
  intro z hz w hw he
  have hz' := (mem_ball_zero_iff.mp hz).le
  have hw' := (mem_ball_zero_iff.mp hw).le
  have hd := (div_eq_div_iff (diskMobius_den_ne_zero ha hz')
    (diskMobius_den_ne_zero ha hw')).mp he
  have hprod : (1 - conj a * a) * (z - w) = 0 := by
    linear_combination hd
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (diskMobius_den_ne_zero ha ha.le))

@[simp] theorem diskMobius_self (a : ℂ) : diskMobius a a = 0 := by simp [diskMobius]

@[simp] theorem diskMobius_zero (a : ℂ) : diskMobius a 0 = -a := by simp [diskMobius]

theorem diskMobius_norm_deriv {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖deriv (diskMobius a) z‖ = (1 - ‖a‖ ^ 2) / ‖1 - conj a * z‖ ^ 2 := by
  rw [(diskMobius_hasDerivAt ha hz).deriv, norm_div, norm_pow]
  congr 1
  rw [mul_comm (conj a), Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by nlinarith [norm_nonneg a] : 0 < 1 - ‖a‖ ^ 2)]

theorem diskMobius_norm_deriv_zero {a : ℂ} (ha : ‖a‖ < 1) :
    ‖deriv (diskMobius a) 0‖ = 1 - ‖a‖ ^ 2 := by
  rw [diskMobius_norm_deriv ha (by simp)]
  simp

theorem diskMobius_norm_deriv_self {a : ℂ} (ha : ‖a‖ < 1) :
    ‖deriv (diskMobius a) a‖ = (1 - ‖a‖ ^ 2)⁻¹ := by
  rw [diskMobius_norm_deriv ha ha.le]
  have hd : ‖1 - conj a * a‖ = 1 - ‖a‖ ^ 2 := by
    rw [mul_comm (conj a), Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by nlinarith [norm_nonneg a] : 0 < 1 - ‖a‖ ^ 2)]
  rw [hd]
  field_simp

theorem hasDerivAt_squareRoot {g F : ℂ → ℂ} {x d : ℂ}
    (hg : ContinuousAt g x) (hg0 : g x ≠ 0) (hF : HasDerivAt F d x)
    (he : ∀ z, g z ^ 2 = F z) : HasDerivAt g (d / (2 * g x)) x := by
  have hn : g x + g x ≠ 0 := by simpa [← two_mul] using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hg0
  have ht := hF.tendsto_slope.div
    ((hg.add_const (g x)).tendsto.mono_left nhdsWithin_le_nhds) hn
  rw [hasDerivAt_iff_tendsto_slope]
  convert ht.congr' ?_ using 1
  · congr 1
    ring
  have hnear : ∀ᶠ z in 𝓝[≠] x, g z + g x ≠ 0 :=
    ((hg.add_const (g x)).eventually_ne hn).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear] with z hz
  simp only [Pi.div_apply, slope, smul_eq_mul, vsub_eq_sub]
  rw [← he z, ← he x]
  field_simp [hz]
  ring

theorem improve_embedding {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U)
    {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    {b : ℂ} (hb : ‖b‖ < 1) (hmiss : b ∉ f '' U) :
    ∃ G, NormalizedEmbedding U a G ∧ ‖deriv f a‖ < ‖deriv G a‖ := by
  have hfb : ∀ z ∈ U, f z ≠ b := by
    intro z hz he
    exact hmiss ⟨z, hz, he⟩
  let H : ℂ → ℂ := diskMobius b ∘ f
  have hH' (z : ℂ) (hz : z ∈ U) :
      HasDerivAt H (deriv (diskMobius b) (f z) * deriv f z) z :=
    ((diskMobius_hasDerivAt hb (mem_ball_zero_iff.mp (hf.disk hz)).le).differentiableAt.hasDerivAt).comp z
      (hf.holomorphic.hasDerivAt (hU.mem_nhds hz))
  have hHd : DifferentiableOn ℂ H U := fun z hz =>
    (hH' z hz).differentiableAt.differentiableWithinAt
  have hHdisk : MapsTo H U (ball 0 1) := (diskMobius_mapsTo hb).comp hf.disk
  have hHi : InjOn H U := (diskMobius_injOn hb).comp hf.injective hf.disk
  have hH0 : ∀ z ∈ U, H z ≠ 0 := by
    intro z hz
    dsimp [H, diskMobius, Function.comp_def]
    exact div_ne_zero (sub_ne_zero.mpr (hfb z hz))
      (diskMobius_den_ne_zero hb (mem_ball_zero_iff.mp (hf.disk hz)).le)
  obtain ⟨g, hgc, hge⟩ := Complex.exists_continuousOn_pow_eq hUc hU hHd.continuousOn
    (by rintro ⟨z, hz, he⟩; exact hH0 z hz he) (by norm_num : (2 : ℕ) ≠ 0)
  have hg0 : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz he
    have ht := hge z
    simp only [he, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at ht
    exact hH0 z hz ht.symm
  have hgd (z : ℂ) (hz : z ∈ U) :
      HasDerivAt g (deriv H z / (2 * g z)) z :=
    hasDerivAt_squareRoot (hgc.continuousAt (hU.mem_nhds hz)) (hg0 z hz)
      (hHd.hasDerivAt (hU.mem_nhds hz)) hge
  have hgi : InjOn g U := by
    intro z hz w hw he
    apply hHi hz hw
    rw [← hge z, ← hge w, he]
  have hgb : MapsTo g U (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff]
    have hn := congrArg norm (hge z)
    rw [norm_pow] at hn
    have ht : ‖H z‖ < 1 := mem_ball_zero_iff.mp (hHdisk hz)
    nlinarith [sq_nonneg (‖g z‖ - 1)]
  have hgne (z : ℂ) (hz : z ∈ U) : deriv g z ≠ 0 := by
    rw [(hgd z hz).deriv, (hH' z hz).deriv]
    exact div_ne_zero (mul_ne_zero
      (diskMobius_deriv_ne_zero hb (mem_ball_zero_iff.mp (hf.disk hz)).le)
      (hf.derivative z hz)) (mul_ne_zero (by norm_num) (hg0 z hz))
  have hr : ‖g a‖ < 1 := mem_ball_zero_iff.mp (hgb ha)
  have hr0 : 0 < ‖g a‖ := norm_pos_iff.mpr (hg0 a ha)
  let G : ℂ → ℂ := diskMobius (g a) ∘ g
  have hG' (z : ℂ) (hz : z ∈ U) :
      HasDerivAt G (deriv (diskMobius (g a)) (g z) * deriv g z) z :=
    ((diskMobius_hasDerivAt hr (mem_ball_zero_iff.mp (hgb hz)).le).differentiableAt.hasDerivAt).comp z
      (hgd z hz).differentiableAt.hasDerivAt
  have hGN : NormalizedEmbedding U a G := by
    refine ⟨fun z hz => (hG' z hz).differentiableAt.differentiableWithinAt,
      (diskMobius_mapsTo hr).comp hgb, (diskMobius_injOn hr).comp hgi hgb, ?_, ?_⟩
    · intro z hz
      rw [(hG' z hz).deriv]
      exact mul_ne_zero (diskMobius_deriv_ne_zero hr (mem_ball_zero_iff.mp (hgb hz)).le)
        (hgne z hz)
    · exact diskMobius_self _
  refine ⟨G, hGN, ?_⟩
  have hab : ‖g a‖ ^ 2 = ‖b‖ := by
    have ht := congrArg norm (hge a)
    simpa only [norm_pow, H, Function.comp_apply, hf.normalized, diskMobius_zero, norm_neg] using ht
  have hval : ‖deriv G a‖ = (1 - ‖g a‖ ^ 2)⁻¹ *
      ((1 - ‖b‖ ^ 2) * ‖deriv f a‖ / (2 * ‖g a‖)) := by
    rw [(hG' a ha).deriv, norm_mul, diskMobius_norm_deriv_self hr,
      (hgd a ha).deriv, norm_div, (hH' a ha).deriv, norm_mul, hf.normalized,
      diskMobius_norm_deriv_zero hb, norm_mul]
    norm_num
  rw [hval]
  have hp : 0 < ‖deriv f a‖ := norm_pos_iff.mpr (hf.derivative a ha)
  have h1 : 0 < 1 - ‖g a‖ ^ 2 := by nlinarith
  have he : (1 - ‖g a‖ ^ 2)⁻¹ *
      ((1 - ‖b‖ ^ 2) * ‖deriv f a‖ / (2 * ‖g a‖)) =
      ((1 + ‖g a‖ ^ 2) / (2 * ‖g a‖)) * ‖deriv f a‖ := by
    rw [← hab]
    field_simp
    ring
  rw [he]
  have hc : 1 < (1 + ‖g a‖ ^ 2) / (2 * ‖g a‖) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hr)]
  nlinarith

theorem exists_riemannMap {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedEmbedding U a f ∧ f '' U = ball 0 1 := by
  obtain ⟨f, hf, hmax⟩ := exists_extremalEmbedding hU hUc hproper ha
  refine ⟨f, hf, Subset.antisymm (by simpa using hf.disk.image_subset) ?_⟩
  intro b hb
  by_contra hmiss
  obtain ⟨G, hG, hlt⟩ := improve_embedding hU hUc ha hf (mem_ball_zero_iff.mp hb) hmiss
  exact (not_lt_of_ge (hmax G hG)) hlt

theorem inverse_hasStrictDerivAt {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {z : ℂ} (hz : z ∈ U) (hd : deriv f z ≠ 0) :
    HasStrictDerivAt (Function.invFunOn f U) (deriv f z)⁻¹ (f z) := by
  apply ((hf.analyticOnNhd hU) z hz).hasStrictDerivAt.to_local_left_inverse hd
  filter_upwards [hU.mem_nhds hz] with w hw
  exact hi.leftInvOn_invFunOn hw

theorem inverse_holomorphic {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f) :
    DifferentiableOn ℂ (Function.invFunOn f U) (f '' U) := by
  rintro y ⟨z, hz, rfl⟩
  exact (inverse_hasStrictDerivAt hU hf.holomorphic hf.injective hz (hf.derivative z hz)).hasDerivAt.differentiableAt.differentiableWithinAt

theorem compact_inverse_disk {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) {r : ℝ} (hr : r < 1) :
    IsCompact (Function.invFunOn f U '' closedBall 0 r) ∧
      Function.invFunOn f U '' closedBall 0 r ⊆ U := by
  have hsub : closedBall (0 : ℂ) r ⊆ f '' U := by
    rw [hs]
    apply closedBall_subset_ball
    exact hr
  refine ⟨(isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
    ((inverse_holomorphic hU hf).continuousOn.mono hsub), ?_⟩
  rintro z ⟨w, hw, rfl⟩
  exact Function.invFunOn_mem (hsub hw)

theorem norm_tendsto_one_boundary {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) {p : ℂ} (hp : p ∉ U) :
    Tendsto (fun z => ‖f z‖) (𝓝[U] p) (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro r hr
    have hc := compact_inverse_disk hU hf hs hr
    have hpn : p ∉ Function.invFunOn f U '' closedBall 0 r := fun h => hp (hc.2 h)
    have he : ∀ᶠ z in 𝓝 p, z ∉ Function.invFunOn f U '' closedBall 0 r :=
      hc.1.isClosed.isOpen_compl.mem_nhds hpn
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzU
    by_contra hn
    apply hz
    refine ⟨f z, ?_, hf.injective.leftInvOn_invFunOn hzU⟩
    simpa using le_of_not_gt hn
  · intro r hr
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (mem_ball_zero_iff.mp (hf.disk hz)).trans hr

open InnerProductSpace Real

end Conformal

end DirectCrouzeix

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/PoissonBoundary.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

open InnerProductSpace Real

def poissonExtension (R : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  Real.circleAverage (fun ζ => poissonKernel 0 z ζ * u ζ) 0 R

theorem poisson_continuous_circle {R : ℝ} {z : ℂ} (hz : z ∈ ball 0 R) :
    ContinuousOn (poissonKernel 0 z) (sphere 0 |R|) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  exact Complex.continuous_re.comp_continuousOn
    (continuousOn_herglotzRieszKernel_sphere
      (by simpa using (mem_ball_zero_iff.mp hz)))

theorem poisson_nonnegative_circle {R : ℝ} {z ζ : ℂ}
    (hz : z ∈ ball 0 R) (hζ : ζ ∈ sphere 0 R) : 0 ≤ poissonKernel 0 z ζ := by
  have hz' := mem_ball_zero_iff.mp hz
  have hζ' : ‖ζ‖ = R := by simpa using hζ
  dsimp [poissonKernel]
  simp only [sub_zero]
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg z]

theorem poisson_average_one {R : ℝ} {z : ℂ} (hz : z ∈ ball 0 R) :
    Real.circleAverage (poissonKernel 0 z) 0 R = 1 := by
  simpa only [Pi.smul_def, Pi.mul_def, smul_eq_mul, mul_one] using (harmonicContOnCl_const (c := (1 : ℝ))
    (s := ball 0 R)).circleAverage_poissonKernel_smul hz

theorem poisson_boundary_limit {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) {p : ℂ} (hp : p ∈ sphere 0 R) :
    Tendsto (poissonExtension R u) (𝓝[ball 0 R] p) (𝓝 (u p)) := by
  have hp' : ‖p‖ = R := by simpa using hp
  have huabs : ContinuousOn (fun ζ => |u ζ - u p|) (sphere 0 R) :=
    (hu.sub continuousOn_const).abs
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn huabs
  have hM0 : 0 ≤ M := (norm_nonneg (|u p - u p|)).trans (hM p hp)
  have hbound : ∀ ζ ∈ sphere 0 R, |u ζ - u p| ≤ M := by
    intro ζ hζ
    simpa only [Real.norm_eq_abs, abs_abs] using hM ζ hζ
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp (hu p hp) (ε / 2) (half_pos hε)
  let C := 4 * M / δ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnear : ∀ᶠ z in 𝓝[ball 0 R] p, dist z p < δ / 2 :=
    (show ∀ᶠ z in 𝓝 p, dist z p < δ / 2 from ball_mem_nhds p (half_pos hδ)).filter_mono nhdsWithin_le_nhds
  have hsmall : ∀ᶠ z in 𝓝[ball 0 R] p, C * (R ^ 2 - ‖z‖ ^ 2) < ε / 2 := by
    have ht : Tendsto (fun z : ℂ => C * (R ^ 2 - ‖z‖ ^ 2)) (𝓝 p) (𝓝 0) := by
      simpa only [hp', sub_self, mul_zero] using
        ((show Continuous (fun z : ℂ => C * (R ^ 2 - ‖z‖ ^ 2)) from by fun_prop).tendsto p)
    exact (ht.eventually (gt_mem_nhds (half_pos hε))).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear, hsmall, self_mem_nhdsWithin] with z hz hzs hzU
  have hP : ContinuousOn (poissonKernel 0 z) (sphere 0 R) := by
    simpa only [abs_of_pos hR] using poisson_continuous_circle hzU
  have hn (ζ : ℂ) (hζ : ζ ∈ sphere 0 R) := poisson_nonnegative_circle hzU hζ
  have hL : 0 ≤ R ^ 2 - ‖z‖ ^ 2 := by
    have hh := mem_ball_zero_iff.mp hzU
    nlinarith [norm_nonneg z]
  have hest : ∀ ζ ∈ sphere 0 R,
      poissonKernel 0 z ζ * |u ζ - u p| ≤
        poissonKernel 0 z ζ * (ε / 2) + C * (R ^ 2 - ‖z‖ ^ 2) := by
    intro ζ hζ
    by_cases hclose : dist ζ p < δ
    · have hd' : |u ζ - u p| < ε / 2 := by
        simpa only [Real.dist_eq] using hd hζ hclose
      have hh := mul_le_mul_of_nonneg_left hd'.le (hn ζ hζ)
      have hh' : 0 ≤ C * (R ^ 2 - ‖z‖ ^ 2) := mul_nonneg hC hL
      linarith
    · have hζnorm : ‖ζ‖ = R := by simpa using hζ
      have hdist : δ / 2 ≤ ‖ζ - z‖ := by
        have hh := dist_triangle ζ z p
        rw [dist_eq_norm ζ z] at hh
        linarith [le_of_not_gt hclose]
      have hden : 0 < ‖ζ - z‖ ^ 2 := sq_pos_of_pos ((half_pos hδ).trans_le hdist)
      have hpk : poissonKernel 0 z ζ ≤ 4 * (R ^ 2 - ‖z‖ ^ 2) / δ ^ 2 := by
        dsimp [poissonKernel]
        simp only [sub_zero, hζnorm]
        rw [div_le_div_iff₀ hden (sq_pos_of_pos hδ)]
        have hden' : δ ^ 2 ≤ 4 * ‖ζ - z‖ ^ 2 := by nlinarith
        nlinarith [mul_nonneg hL (sub_nonneg.mpr hden')]
      have hh := mul_le_mul (hbound ζ hζ) hpk (hn ζ hζ) hM0
      have hright : 0 ≤ poissonKernel 0 z ζ * (ε / 2) := mul_nonneg (hn ζ hζ) (half_pos hε).le
      dsimp [C]
      have halg : M * (4 * (R ^ 2 - ‖z‖ ^ 2) / δ ^ 2) =
          4 * M / δ ^ 2 * (R ^ 2 - ‖z‖ ^ 2) := by ring
      rw [mul_comm |u ζ - u p|, halg] at hh
      linarith
  have hi : CircleIntegrable (fun ζ => poissonKernel 0 z ζ * (u ζ - u p)) 0 R :=
    (hP.mul (hu.sub continuousOn_const)).circleIntegrable hR.le
  have heq : poissonExtension R u z - u p =
      Real.circleAverage (fun ζ => poissonKernel 0 z ζ * (u ζ - u p)) 0 R := by
    dsimp [poissonExtension]
    have ht := Real.circleAverage_fun_sub
      (f₁ := fun ζ => poissonKernel 0 z ζ * u ζ)
      (f₂ := fun ζ => poissonKernel 0 z ζ * u p)
      ((hP.mul hu).circleIntegrable hR.le)
      ((hP.mul_const (u p)).circleIntegrable hR.le)
    simp_rw [mul_sub]
    rw [ht]
    congr 1
    simp_rw [mul_comm _ (u p), ← smul_eq_mul]
    rw [Real.circleAverage_fun_smul, poisson_average_one hzU, smul_eq_mul, mul_one]
  rw [Real.dist_eq, heq]
  calc
    |Real.circleAverage (fun ζ => poissonKernel 0 z ζ * (u ζ - u p)) 0 R|
        ≤ Real.circleAverage (fun ζ => |poissonKernel 0 z ζ * (u ζ - u p)|) 0 R :=
      Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage
        (fun ζ => poissonKernel 0 z ζ * (ε / 2) + C * (R ^ 2 - ‖z‖ ^ 2)) 0 R := by
      apply Real.circleAverage_mono hi.abs
        (((hP.mul_const (ε / 2)).add_const _).circleIntegrable hR.le)
      intro ζ hζ
      have hζ' : ζ ∈ sphere 0 R := by simpa only [abs_of_pos hR] using hζ
      change |poissonKernel 0 z ζ * (u ζ - u p)| ≤ _
      rw [abs_mul, abs_of_nonneg (hn ζ hζ')]
      exact hest ζ hζ'
    _ = ε / 2 + C * (R ^ 2 - ‖z‖ ^ 2) := by
      rw [Real.circleAverage_fun_add ((hP.mul_const (ε / 2)).circleIntegrable hR.le)
        (by exact continuousOn_const.circleIntegrable hR.le), Real.circleAverage_const]
      congr 1
      simp_rw [mul_comm _ (ε / 2), ← smul_eq_mul]
      rw [Real.circleAverage_fun_smul, poisson_average_one hzU, smul_eq_mul, mul_one]
    _ < ε := by linarith

theorem harmonic_eventually_eq_of_isLocalMax {u : ℂ → ℝ} {a : ℂ}
    (hu : HarmonicAt u a) (hm : IsLocalMax u a) :
    u =ᶠ[𝓝 a] (fun _ => u a) := by
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp (isOpen_setOfPred_harmonicAt u) a hu
  obtain ⟨F, hF, hRe⟩ := (show HarmonicOnNhd u (ball a r) from hB).exists_analyticOnNhd_ball_re_eq
  have hd : ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ (fun z => Complex.exp (F z)) z := by
    filter_upwards [ball_mem_nhds a hr] with z hz
    exact (hF z hz).differentiableAt.cexp
  have hmax : IsLocalMax (norm ∘ (fun z => Complex.exp (F z))) a := by
    filter_upwards [hm, ball_mem_nhds a hr] with z hz hzB
    simpa only [Function.comp_apply, Complex.norm_exp, hRe hzB,
      hRe (mem_ball_self hr), Real.exp_le_exp] using hz
  have he := Complex.norm_eventually_eq_of_isLocalMax hd hmax
  filter_upwards [he, ball_mem_nhds a hr] with z hz hzB
  simpa only [Complex.norm_exp, hRe hzB, hRe (mem_ball_self hr), Real.exp_eq_exp] using hz

theorem harmonic_le_boundary {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) {u : ℂ → ℝ}
    (hu : HarmonicContOnCl u U) {M : ℝ}
    (hM : ∀ z ∈ frontier U, u z ≤ M) :
    ∀ z ∈ closure U, u z ≤ M := by
  intro z hz
  by_contra hle
  obtain ⟨a, ha, hmax⟩ := hb.isCompact_closure.exists_isMaxOn ⟨z, hz⟩ hu.2
  have hhigh : M < u a := (lt_of_not_ge hle).trans_le (hmax hz)
  let S := {x ∈ closure U | u x = u a}
  have hSc : IsCompact S := by
    exact hb.isCompact_closure.of_isClosed_subset
      (hu.2.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton) (by intro x hx; exact hx.1)
  have hSo : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hxU : x ∈ U := by
      by_contra hn
      have hf : x ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hx.1, hn⟩
      exact (not_le_of_gt hhigh) (hx.2 ▸ hM x hf)
    have hxmax : IsLocalMax u x := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact hx.2 ▸ hmax (subset_closure hy)
    have he := harmonic_eventually_eq_of_isLocalMax (hu.1 x hxU) hxmax
    filter_upwards [he, hU.mem_nhds hxU] with y hy hyU
    exact ⟨subset_closure hyU, hy.trans hx.2⟩
  have hSne : S.Nonempty := ⟨a, ha, rfl⟩
  have hSun : S = univ := (show IsClopen S from ⟨hSc.isClosed, hSo⟩).eq_univ hSne
  exact hSc.ne_univ hSun

def herglotzExtension (R : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℂ :=
  Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ * (u ζ : ℂ)) 0 R

theorem herglotz_analytic {R : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) :
    AnalyticOnNhd ℂ (herglotzExtension R u) (ball 0 R) := by
  exact (analyticOnNhd_circleAverage_herglotzRieszKernel_smul
    ((Complex.continuous_ofReal.comp_continuousOn hu).circleIntegrable hR)).mono
      (by intro z hz; simpa [abs_of_nonneg hR] using (mem_ball_zero_iff.mp hz))

theorem herglotz_re {R : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) {z : ℂ} (hz : z ∈ ball 0 R) :
    (herglotzExtension R u z).re = poissonExtension R u z := by
  have hi : CircleIntegrable
      (fun ζ => herglotzRieszKernel 0 z ζ * (u ζ : ℂ)) 0 R := by
    exact ((continuousOn_herglotzRieszKernel_sphere
      (by simpa [abs_of_nonneg hR] using (mem_ball_zero_iff.mp hz))).mul
      (Complex.continuous_ofReal.comp_continuousOn (by simpa only [abs_of_nonneg hR] using hu))).circleIntegrable'
  change Complex.reCLM (Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ * (u ζ : ℂ)) 0 R) = _
  rw [← Complex.reCLM.circleAverage_comp_comm hi]
  dsimp [poissonExtension]
  congr 1
  ext ζ
  simp [poissonKernel_eq_re_herglotzRieszKernel]

theorem poisson_harmonic {R : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) :
    HarmonicOnNhd (poissonExtension R u) (ball 0 R) := by
  intro z hz
  have he : (poissonExtension R u) =ᶠ[𝓝 z]
      (fun w => (herglotzExtension R u w).re) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact (herglotz_re hR hu hw).symm
  rw [harmonicAt_congr_nhds he]
  exact ((herglotz_analytic hR hu z hz).harmonicAt.comp_CLM Complex.reCLM)

end Conformal

end DirectCrouzeix

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/HarmonicReflection.lean
section
namespace OAI

universe u_132

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

open InnerProductSpace Real

theorem circleAverage_conj {E : Type u_132} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (R : ℝ) :
    Real.circleAverage (fun ζ => f (conj ζ)) 0 R = Real.circleAverage f 0 R := by
  conv_lhs => rw [Real.circleAverage_eq_circleAverage_zero_one]
  conv_rhs => rw [Real.circleAverage_eq_circleAverage_zero_one]
  calc
    Real.circleAverage (fun z => f (conj ((R : ℂ) * z + 0))) 0 1 =
        Real.circleAverage (fun z => f ((R : ℂ) * z⁻¹ + 0)) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hn : ‖z‖ = 1 := by simpa using hz
      simp [Complex.inv_eq_conj hn]
    _ = Real.circleAverage (fun z => f ((R : ℂ) * z + 0)) 0 1 :=
      Real.circleAverage_zero_one_congr_inv (f := fun z => f ((R : ℂ) * z + 0))

theorem poisson_conj (z ζ : ℂ) :
    poissonKernel 0 (conj z) (conj ζ) = poissonKernel 0 z ζ := by
  simp only [poissonKernel, sub_zero, Complex.norm_conj, ← map_sub]

theorem poisson_odd {R : ℝ} {u : ℂ → ℝ}
    (hu : ∀ ζ, u (conj ζ) = -u ζ) (z : ℂ) :
    poissonExtension R u (conj z) = -poissonExtension R u z := by
  dsimp [poissonExtension]
  rw [← circleAverage_conj (fun ζ => poissonKernel 0 (conj z) ζ * u ζ) R]
  simp_rw [poisson_conj, hu, mul_neg]
  have he (ζ : ℂ) : -(poissonKernel 0 z ζ * u ζ) = (-1 : ℝ) • (poissonKernel 0 z ζ * u ζ) := by simp
  simp_rw [he]
  rw [Real.circleAverage_fun_smul, neg_one_smul]

theorem poisson_real_zero {R : ℝ} {u : ℂ → ℝ}
    (hu : ∀ ζ, u (conj ζ) = -u ζ) {z : ℂ} (hz : z.im = 0) :
    poissonExtension R u z = 0 := by
  have hc : conj z = z := Complex.conj_eq_iff_im.mpr hz
  have hh := poisson_odd (R := R) hu z
  rw [hc] at hh
  linarith

def poissonClosed (R : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ := by
  classical
  exact if z ∈ ball 0 R then poissonExtension R u z else u z

theorem poissonClosed_continuous {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) :
    ContinuousOn (poissonClosed R u) (closedBall 0 R) := by
  classical
  unfold poissonClosed
  apply ContinuousOn.if'
  · intro a ha
    have haS : a ∈ sphere 0 R := by
      simpa only [Set.ofPred_mem_eq, frontier_ball (0 : ℂ) hR.ne'] using ha.2
    have haN : a ∉ ball 0 R := fun h => sphere_disjoint_ball.le_bot ⟨haS, h⟩
    simp only [haN, ↓reduceIte]
    exact (poisson_boundary_limit hR hu haS).mono_left (nhdsWithin_mono _ inter_subset_right)
  · intro a ha
    have haS : a ∈ sphere 0 R := by
      simpa only [Set.ofPred_mem_eq, frontier_ball (0 : ℂ) hR.ne'] using ha.2
    have haN : a ∉ ball 0 R := fun h => sphere_disjoint_ball.le_bot ⟨haS, h⟩
    simp only [haN, ↓reduceIte]
    apply (hu a haS).mono
    intro z hz
    exact le_antisymm (mem_closedBall.mp hz.1) (not_lt.mp hz.2)
  · exact (poisson_harmonic hR.le hu).continuousOn.mono inter_subset_right
  · apply hu.mono
    intro z hz
    exact le_antisymm (mem_closedBall.mp hz.1) (not_lt.mp hz.2)

def upperBall (R : ℝ) : Set ℂ := ball 0 R ∩ {z | 0 < z.im}

def upperClosedBall (R : ℝ) : Set ℂ := closedBall 0 R ∩ {z | 0 ≤ z.im}

theorem upperBall_open (R : ℝ) : IsOpen (upperBall R) :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

theorem upperClosedBall_closed (R : ℝ) : IsClosed (upperClosedBall R) :=
  isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)

theorem closure_upperBall_subset (R : ℝ) : closure (upperBall R) ⊆ upperClosedBall R := by
  apply closure_minimal _ (upperClosedBall_closed R)
  intro z hz
  exact ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩

def oddUpper (u : ℂ → ℝ) (z : ℂ) : ℝ := if 0 ≤ z.im then u z else -u (conj z)

theorem oddUpper_conj {u : ℂ → ℝ} (hzero : ∀ z, z.im = 0 → u z = 0)
    (z : ℂ) : oddUpper u (conj z) = -oddUpper u z := by
  dsimp [oddUpper]
  rw [Complex.conj_conj]
  change (if 0 ≤ -z.im then u (conj z) else -u z) = -(if 0 ≤ z.im then u z else -u (conj z))
  by_cases hz : z.im = 0
  · have hc : conj z = z := Complex.conj_eq_iff_im.mpr hz
    simp [hz, hc, hzero z hz]
  · by_cases hh : 0 ≤ z.im
    · have hn : ¬ 0 ≤ -z.im := fun he => hz (by linarith)
      rw [if_neg hn, if_pos hh]
    · rw [if_pos (show 0 ≤ -z.im by linarith), if_neg hh, neg_neg]

theorem oddUpper_continuous_circle {R : ℝ} {u : ℂ → ℝ}
    (hu : ContinuousOn u (upperClosedBall R))
    (hzero : ∀ z, z.im = 0 → u z = 0) :
    ContinuousOn (oddUpper u) (sphere 0 R) := by
  classical
  apply ContinuousOn.if
  · intro z hz
    have hfr := Complex.continuous_im.frontier_preimage_subset (Ici (0 : ℝ)) hz.2
    have hz0 : z.im = 0 := by simpa only [frontier_Ici, mem_preimage, mem_singleton_iff] using hfr
    have hc : conj z = z := Complex.conj_eq_iff_im.mpr hz0
    simp [hc, hzero z hz0]
  · apply hu.mono
    intro z hz
    have hi : 0 ≤ z.im := by
      exact (closure_minimal (by intro w hw; exact hw)
        (isClosed_le continuous_const Complex.continuous_im)) hz.2
    exact ⟨sphere_subset_closedBall hz.1, hi⟩
  · apply ContinuousOn.neg
    apply hu.comp Complex.continuous_conj.continuousOn
    intro z hz
    have hi : z.im ≤ 0 := by
      exact (closure_minimal (by intro w hw; exact (le_of_not_ge hw))
        (isClosed_le Complex.continuous_im continuous_const)) hz.2
    exact ⟨by simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using
      sphere_subset_closedBall hz.1, by simpa only [mem_ofPred_eq, Complex.conj_im, neg_nonneg] using hi⟩

theorem harmonic_reflection {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (upperBall R))
    (huc : ContinuousOn u (upperClosedBall R))
    (hzero : ∀ z, z.im = 0 → u z = 0) :
    EqOn (fun z => (herglotzExtension R (oddUpper u) z).re) u (upperBall R) := by
  let v := oddUpper u
  have hvc : ContinuousOn v (sphere 0 R) := oddUpper_continuous_circle huc hzero
  let w := poissonClosed R v
  have hwc := poissonClosed_continuous hR hvc
  have he : EqOn w (poissonExtension R v) (ball 0 R) := by
    intro z hz
    simp [w, poissonClosed, hz]
  have hwh : HarmonicOnNhd w (ball 0 R) := by
    intro z hz
    rw [harmonicAt_congr_nhds (he.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz))]
    exact poisson_harmonic hR.le hvc z hz
  have hdiff : HarmonicContOnCl (u - w) (upperBall R) := by
    refine ⟨hu.sub (hwh.mono inter_subset_left), ?_⟩
    exact (huc.mono (closure_upperBall_subset R)).sub
      (hwc.mono ((closure_upperBall_subset R).trans inter_subset_left))
  have hbound : EqOn (u - w) 0 (frontier (upperBall R)) := by
    intro z hz
    have hzK := closure_upperBall_subset R hz.1
    have hn : z ∉ upperBall R := by
      simpa only [(upperBall_open R).interior_eq] using hz.2
    by_cases hzB : z ∈ ball 0 R
    · have hz0 : z.im = 0 := le_antisymm (le_of_not_gt (fun hi => hn ⟨hzB, hi⟩)) hzK.2
      have hw0 : w z = 0 := by
        rw [he hzB]
        exact poisson_real_zero (oddUpper_conj hzero) hz0
      simp [hzero z hz0, hw0]
    · have hi : 0 ≤ z.im := hzK.2
      simp [w, poissonClosed, hzB, v, oddUpper, hi]
  have hb : Bornology.IsBounded (upperBall R) := isBounded_ball.subset inter_subset_left
  have hlo := harmonic_le_boundary (upperBall_open R) hb hdiff (M := 0)
    (fun z hz => le_of_eq (hbound hz))
  have hhi := harmonic_le_boundary (upperBall_open R) hb hdiff.neg (M := 0)
    (fun z hz => by simp [hbound hz])
  intro z hz
  change (herglotzExtension R v z).re = u z
  rw [herglotz_re hR.le hvc hz.1, ← he hz.1]
  have ha := hlo z (subset_closure hz)
  have hb := hhi z (subset_closure hz)
  change u z - w z ≤ 0 at ha
  change -(u z - w z) ≤ 0 at hb
  linarith

end Conformal

end DirectCrouzeix

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/HolomorphicReflection.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

open InnerProductSpace Real

def logModulusUpper (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  if 0 < z.im then Real.log ‖f z‖ else 0

theorem logModulusUpper_real {f : ℂ → ℂ} {z : ℂ} (hz : z.im = 0) :
    logModulusUpper f z = 0 := by simp [logModulusUpper, hz]

theorem logModulusUpper_continuous {R : ℝ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (closedBall 0 R ∩ {z | 0 < z.im}))
    (hn : ∀ z ∈ closedBall 0 R ∩ {z | 0 < z.im}, f z ≠ 0)
    (hl : ∀ z ∈ closedBall 0 R, z.im = 0 →
      Tendsto (fun w => ‖f w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 1)) :
    ContinuousOn (logModulusUpper f) (upperClosedBall R) := by
  unfold logModulusUpper
  apply ContinuousOn.if'
  · intro z hz
    have hf := Complex.continuous_im.frontier_preimage_subset (Ioi (0 : ℝ)) hz.2
    have hz0 : z.im = 0 := by simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using hf
    simp only [hz0, lt_self_iff_false, ↓reduceIte]
    have ht : Tendsto (fun w => Real.log ‖f w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 0) := by
      simpa only [Function.comp_def, Real.log_one] using (Real.continuousAt_log one_ne_zero).tendsto.comp (hl z hz.1.1 hz0)
    exact ht.mono_left (nhdsWithin_mono _ inter_subset_right)
  · intro z hz
    have hf := Complex.continuous_im.frontier_preimage_subset (Ioi (0 : ℝ)) hz.2
    have hz0 : z.im = 0 := by simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using hf
    simp only [hz0, lt_self_iff_false, ↓reduceIte]
    exact tendsto_const_nhds
  · apply (hc.norm.log (fun z hz => norm_ne_zero_iff.mpr (hn z hz))).mono
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  · exact continuousOn_const

theorem upperBall_convex (R : ℝ) : Convex ℝ (upperBall R) :=
  (convex_ball (0 : ℂ) R).inter (convex_Ioi (0 : ℝ) |>.linear_preimage Complex.imCLM.toLinearMap)

theorem upperBall_half_radius {R : ℝ} (hR : 0 < R) :
    ((R / 2 : ℝ) : ℂ) * Complex.I ∈ upperBall R := by
  constructor
  · simp only [mem_ball_zero_iff, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (half_pos hR)]
    linarith
  · simpa using half_pos hR

theorem circleAverage_pos_upper {R : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R))
    (hn : ∀ z ∈ sphere 0 R, 0 ≤ u z) (hp : 0 < u ((R : ℂ) * Complex.I)) :
    0 < Real.circleAverage u 0 R := by
  have hall (θ : ℝ) : circleMap 0 R θ ∈ sphere 0 R := by
    simpa only [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ
  have hc : Continuous (fun θ => u (circleMap 0 R θ)) :=
    hu.comp_continuous (continuous_circleMap 0 R) hall
  have hip : 0 < ∫ θ in (0 : ℝ)..2 * Real.pi, u (circleMap 0 R θ) := by
    apply intervalIntegral.integral_pos Real.two_pi_pos hc.continuousOn
    · intro θ _
      exact hn _ (hall θ)
    · refine ⟨Real.pi / 2, ⟨by positivity, by nlinarith [Real.pi_pos]⟩, ?_⟩
      simpa only [circleMap_pi_div_two, zero_add] using hp
  exact mul_pos (inv_pos.mpr Real.two_pi_pos) hip

theorem herglotz_deriv_im_pos {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R))
    (hn : ∀ z ∈ sphere 0 R, u z * z.im ≤ 0)
    (hp : u ((R : ℂ) * Complex.I) < 0) :
    0 < (deriv (herglotzExtension R u) 0).im := by
  let d := fun ζ : ℂ => (2 / ζ) * (u ζ : ℂ)
  have hzne : ∀ ζ ∈ sphere 0 R, ζ ≠ (0 : ℂ) := by
    intro ζ hζ hz
    subst ζ
    exact hR.ne' (by simpa only [mem_sphere, dist_self, eq_comm] using hζ)
  have hd : ContinuousOn d (sphere 0 R) :=
    (continuousOn_const.div continuousOn_id hzne).mul (Complex.continuous_ofReal.comp_continuousOn hu)
  have hder := hasDerivAt_circleAverage_herglotzRieszKernel_smul
    ((Complex.continuous_ofReal.comp_continuousOn hu).circleIntegrable hR.le)
    (by simpa using hR : (0 : ℂ) ∈ ball 0 R)
  change HasDerivAt (herglotzExtension R u) _ _ at hder
  have hval : deriv (herglotzExtension R u) 0 = Real.circleAverage d 0 R := by
    rw [hder.deriv]
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    have hz : ζ ≠ 0 := hzne ζ (by simpa only [abs_of_pos hR] using hζ)
    dsimp [d]
    simp only [sub_zero]
    congr 1
    field_simp
  have he (ζ : ℂ) : (d ζ).im = -2 * (u ζ * ζ.im) / Complex.normSq ζ := by
    dsimp [d]
    simp [Complex.mul_im, Complex.div_im]
    ring
  have hnon : ∀ ζ ∈ sphere 0 R, 0 ≤ (d ζ).im := by
    intro ζ hζ
    rw [he]
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (hn ζ hζ))
      (Complex.normSq_nonneg ζ)
  have hpos : 0 < (d ((R : ℂ) * Complex.I)).im := by
    rw [he]
    have him : ((R : ℂ) * Complex.I).im = R := by simp
    rw [him]
    apply div_pos
    · exact mul_pos_of_neg_of_neg (by norm_num) (mul_neg_of_neg_of_pos hp hR)
    · rw [Complex.normSq_pos]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') Complex.I_ne_zero
  rw [hval]
  change 0 < Complex.imCLM (Real.circleAverage d 0 R)
  rw [← Complex.imCLM.circleAverage_comp_comm (hd.circleIntegrable hR.le)]
  exact circleAverage_pos_upper hR.le (Complex.continuous_im.comp_continuousOn hd) hnon hpos

theorem holomorphic_reflection_modulus {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R ∩ {z | 0 < z.im}))
    (hn : ∀ z ∈ closedBall 0 R ∩ {z | 0 < z.im}, f z ≠ 0)
    (hb : ∀ z ∈ closedBall 0 R ∩ {z | 0 < z.im}, ‖f z‖ < 1)
    (hl : ∀ z ∈ closedBall 0 R, z.im = 0 →
      Tendsto (fun w => ‖f w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 1)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball 0 R) ∧ EqOn F f (upperBall R) ∧
      (∀ z ∈ ball 0 R, z.im = 0 → ‖F z‖ = 1) ∧ deriv F 0 ≠ 0 ∧
      (∀ z ∈ ball 0 R, ‖F z‖ < 1 ↔ 0 < z.im) := by
  let u := logModulusUpper f
  let v := oddUpper u
  let H := herglotzExtension R v
  have hu0 : ∀ z, z.im = 0 → u z = 0 := fun _ hz => logModulusUpper_real hz
  have huc := logModulusUpper_continuous hf.continuousOn hn hl
  have hvc : ContinuousOn v (sphere 0 R) := oddUpper_continuous_circle huc hu0
  have hH : AnalyticOnNhd ℂ H (ball 0 R) := herglotz_analytic hR.le hvc
  have hu : HarmonicOnNhd u (upperBall R) := by
    intro z hz
    have hzK : z ∈ closedBall 0 R ∩ {z | 0 < z.im} := ⟨ball_subset_closedBall hz.1, hz.2⟩
    have he : u =ᶠ[𝓝 z] (fun w => Real.log ‖f w‖) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz.2] with w hw
      simp only [u, logModulusUpper, hw, ↓reduceIte]
    rw [harmonicAt_congr_nhds he]
    exact (hf z hzK).harmonicAt_log_norm (hn z hzK)
  have hRe := harmonic_reflection hR hu huc hu0
  let k := fun z => f z * Complex.exp (-H z)
  have hk : DifferentiableOn ℂ k (upperBall R) := by
    apply (hf.differentiableOn.mono (by intro z hz; exact ⟨ball_subset_closedBall hz.1, hz.2⟩)).mul
    exact (hH.differentiableOn.mono inter_subset_left).neg.cexp
  have hkn : ∀ z ∈ upperBall R, ‖k z‖ = 1 := by
    intro z hz
    have hRe' : (H z).re = Real.log ‖f z‖ := by
      have hh : (H z).re = u z := hRe hz
      simpa only [u, logModulusUpper, if_pos (show 0 < z.im from hz.2)] using hh
    have hnz := hn z ⟨ball_subset_closedBall hz.1, hz.2⟩
    dsimp [k]
    rw [norm_mul, Complex.norm_exp, Complex.neg_re, hRe', Real.exp_neg,
      Real.exp_log (norm_pos_iff.mpr hnz), mul_inv_cancel₀ (norm_ne_zero_iff.mpr hnz)]
  let c : ℂ := ((R / 2 : ℝ) : ℂ) * Complex.I
  have hc : c ∈ upperBall R := upperBall_half_radius hR
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (upperBall_convex R).isPreconnected (upperBall_open R) hk hc
    (show IsMaxOn (norm ∘ k) (upperBall R) c from
      fun z hz => by
        change ‖k z‖ ≤ ‖k c‖
        rw [hkn z hz, hkn c hc])
  refine ⟨fun z => k c * Complex.exp (H z), analyticOnNhd_const.mul hH.cexp, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hh : k z = k c := hconst hz
    rw [← hh]
    simp [k, Complex.exp_neg, Complex.exp_ne_zero]
  · intro z hz hz0
    have hHz : (H z).re = 0 := by
      rw [show H z = herglotzExtension R v z from rfl, herglotz_re hR.le hvc hz]
      exact poisson_real_zero (oddUpper_conj hu0) hz0
    rw [norm_mul, hkn c hc, Complex.norm_exp, hHz, Real.exp_zero, mul_one]
  · have hvsign : ∀ z ∈ sphere 0 R, v z * z.im ≤ 0 := by
      intro z hz
      by_cases hi : 0 ≤ z.im
      · by_cases hi0 : z.im = 0
        · simp [hi0]
        · have hip : 0 < z.im := lt_of_le_of_ne hi (Ne.symm hi0)
          have hzK : z ∈ closedBall 0 R ∩ {z | 0 < z.im} := ⟨sphere_subset_closedBall hz, hip⟩
          have huNeg : u z < 0 := by
            simpa only [u, logModulusUpper, if_pos hip] using
              Real.log_neg (norm_pos_iff.mpr (hn z hzK)) (hb z hzK)
          simpa only [v, oddUpper, if_pos hi] using mul_nonpos_of_nonpos_of_nonneg huNeg.le hi
      · have hip : 0 < (conj z).im := by simpa only [Complex.conj_im] using neg_pos.mpr (lt_of_not_ge hi)
        have hzK : conj z ∈ closedBall 0 R ∩ {z | 0 < z.im} :=
          ⟨by simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using sphere_subset_closedBall hz, hip⟩
        have huNeg : u (conj z) < 0 := by
          simpa only [u, logModulusUpper, if_pos hip] using
            Real.log_neg (norm_pos_iff.mpr (hn _ hzK)) (hb _ hzK)
        simpa only [v, oddUpper, if_neg hi] using
          mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr huNeg.le) (le_of_not_ge hi)
    have hvpole : v ((R : ℂ) * Complex.I) < 0 := by
      have hip : 0 < ((R : ℂ) * Complex.I).im := by simpa using hR
      have hzK : (R : ℂ) * Complex.I ∈ closedBall 0 R ∩ {z | 0 < z.im} :=
        ⟨by simp [mem_closedBall, abs_of_pos hR], hip⟩
      simpa only [v, oddUpper, if_pos hip.le, u, logModulusUpper, if_pos hip] using
        Real.log_neg (norm_pos_iff.mpr (hn _ hzK)) (hb _ hzK)
    have hdpos : 0 < (deriv H 0).im := herglotz_deriv_im_pos hR hvc hvsign hvpole
    have hdne : deriv H 0 ≠ 0 := by intro he; simp [he] at hdpos
    have hkc : k c ≠ 0 := by intro he; simpa [he] using hkn c hc
    have hderF := ((hH 0 (mem_ball_self hR)).differentiableAt.hasDerivAt.cexp).const_mul (k c)
    rw [hderF.deriv]
    exact mul_ne_zero hkc (mul_ne_zero (Complex.exp_ne_zero _) hdne)
  · intro z hz
    change ‖k c * Complex.exp (H z)‖ < 1 ↔ 0 < z.im
    by_cases hi : 0 < z.im
    · have hh : k z = k c := hconst ⟨hz, hi⟩
      have he : k c * Complex.exp (H z) = f z := by
        rw [← hh]
        simp [k, Complex.exp_neg, Complex.exp_ne_zero]
      rw [he]
      exact iff_of_true (hb z ⟨ball_subset_closedBall hz, hi⟩) hi
    · by_cases hi0 : z.im = 0
      · have hHz : (H z).re = 0 := by
          rw [show H z = herglotzExtension R v z from rfl, herglotz_re hR.le hvc hz]
          exact poisson_real_zero (oddUpper_conj hu0) hi0
        simp only [norm_mul, hkn c hc, Complex.norm_exp, hHz, Real.exp_zero, mul_one,
          lt_self_iff_false, hi0]
      · have hic : 0 < (conj z).im := by
          simpa only [Complex.conj_im] using
            (neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hi) hi0))
        have hzcb : conj z ∈ ball 0 R := by simpa only [mem_ball_zero_iff, Complex.norm_conj] using hz
        have hzK : conj z ∈ closedBall 0 R ∩ {z | 0 < z.im} := ⟨ball_subset_closedBall hzcb, hic⟩
        have hRc : (H (conj z)).re = Real.log ‖f (conj z)‖ := by
          have hh : (H (conj z)).re = u (conj z) := hRe ⟨hzcb, hic⟩
          simpa only [u, logModulusUpper, if_pos hic] using hh
        have ho : (H (conj z)).re = -(H z).re := by
          change (herglotzExtension R v (conj z)).re = -(herglotzExtension R v z).re
          rw [herglotz_re hR.le hvc hzcb, herglotz_re hR.le hvc hz]
          exact poisson_odd (oddUpper_conj hu0) z
        have hpos : 0 < (H z).re := by
          have hnlog := Real.log_neg (norm_pos_iff.mpr (hn _ hzK)) (hb _ hzK)
          linarith
        have hlarge : 1 < ‖k c * Complex.exp (H z)‖ := by
          rw [norm_mul, hkn c hc, one_mul, Complex.norm_exp]
          exact Real.one_lt_exp_iff.mpr hpos
        exact iff_of_false (not_lt_of_ge hlarge.le) hi

end Conformal

end DirectCrouzeix

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/Continuation.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

open InnerProductSpace Real

theorem boundary_germs_compatible {U : Set ℂ} (hU : IsOpen U)
    {p q z : ℂ} (hp : p ∈ closure U) (hq : q ∈ closure U)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hzp : z ∈ ball p r) (hzq : z ∈ ball q s)
    {E G f : ℂ → ℂ}
    (hE : AnalyticOnNhd ℂ E (ball p (3*r)))
    (hG : AnalyticOnNhd ℂ G (ball q (3*s)))
    (he : EqOn E f (ball p (3*r) ∩ U))
    (hg : EqOn G f (ball q (3*s) ∩ U)) : E z = G z := by
  let V := ball p (3*r) ∩ ball q (3*s)
  have hVo : IsOpen V := isOpen_ball.inter isOpen_ball
  have hmeet : (V ∩ closure U).Nonempty := by
    have hd : dist p q < r + s := by
      have := dist_triangle p z q
      rw [dist_comm p z] at this
      have hpz := mem_ball.mp hzp
      have hqz := mem_ball.mp hzq
      linarith
    rcases le_total r s with hrs | hsr
    · refine ⟨p, ⟨mem_ball_self (by positivity), ?_⟩, hp⟩
      rw [mem_ball]
      linarith
    · refine ⟨q, ⟨?_, mem_ball_self (by positivity)⟩, hq⟩
      rw [mem_ball, dist_comm]
      linarith
  obtain ⟨b, hbV, hbU⟩ := hmeet
  obtain ⟨a, haV, haU⟩ := mem_closure_iff_nhds.mp hbU V (hVo.mem_nhds hbV)
  have heq : E =ᶠ[𝓝 a] G := by
    filter_upwards [(hVo.inter hU).mem_nhds ⟨haV, haU⟩] with w hw
    exact (he ⟨hw.1.1, hw.2⟩).trans (hg ⟨hw.1.2, hw.2⟩).symm
  exact (hE.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
    (hG.mono inter_subset_right)
    ((convex_ball p (3*r)).inter (convex_ball q (3*s))).isPreconnected haV heq
    ⟨ball_subset_ball (by linarith) hzp, ball_subset_ball (by linarith) hzq⟩

theorem patch_boundary_germs {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hloc : ∀ p ∈ closure U, ∃ r > 0, ∃ E : ℂ → ℂ,
      AnalyticOnNhd ℂ E (ball p (3*r)) ∧ EqOn E f (ball p (3*r) ∩ U) ∧
      (∀ z ∈ ball p (3*r), ‖E z‖ < 1 ↔ z ∈ U) ∧ deriv E p ≠ 0) :
    ∃ V : Set ℂ, ∃ F : ℂ → ℂ, IsOpen V ∧ closure U ⊆ V ∧
      AnalyticOnNhd ℂ F V ∧ EqOn F f U ∧
      (∀ z ∈ V, ‖F z‖ < 1 ↔ z ∈ U) ∧ (∀ p ∈ closure U, deriv F p ≠ 0) := by
  classical
  choose r hr E hE he hside hd using hloc
  let V : Set ℂ := ⋃ p : closure U, ball (p : ℂ) (r p p.property)
  have hV : IsOpen V := isOpen_iUnion fun _ => isOpen_ball
  have hUV : closure U ⊆ V := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩, mem_ball_self (hr p hp)⟩
  have hchoose : ∀ z ∈ V, ∃ p : closure U, z ∈ ball (p : ℂ) (r p p.property) := by
    intro z hz
    exact mem_iUnion.mp hz
  let F : ℂ → ℂ := fun z => if hz : z ∈ V then
    E (hchoose z hz).choose (hchoose z hz).choose.property z else f z
  have hFE : ∀ p : closure U, EqOn F (E p p.property) (ball (p : ℂ) (r p p.property)) := by
    intro p z hz
    have hzV : z ∈ V := mem_iUnion.mpr ⟨p,hz⟩
    dsimp only [F]
    rw [dif_pos hzV]
    exact boundary_germs_compatible hU (hchoose z hzV).choose.property p.property
      (hr _ _) (hr _ _) (hchoose z hzV).choose_spec hz
      (hE _ _) (hE _ _) (he _ _) (he _ _)
  refine ⟨V,F,hV,hUV,?_,?_,?_,?_⟩
  · intro z hz
    obtain ⟨p,hp⟩ := hchoose z hz
    apply (hE p p.property z (ball_subset_ball (by linarith [hr p p.property]) hp)).congr
    filter_upwards [isOpen_ball.mem_nhds hp] with w hw
    exact (hFE p hw).symm
  · intro z hz
    exact (hFE ⟨z,subset_closure hz⟩ (mem_ball_self (hr _ _))).trans
      (he z (subset_closure hz) ⟨mem_ball_self (by linarith [hr z (subset_closure hz)]),hz⟩)
  · intro z hz
    obtain ⟨p,hp⟩ := hchoose z hz
    rw [hFE p hp]
    exact hside p p.property z (ball_subset_ball (by linarith [hr p p.property]) hp)
  · intro p hp
    have hevent : F =ᶠ[𝓝 p] E p hp := by
      filter_upwards [ball_mem_nhds p (hr p hp)] with z hz
      exact hFE ⟨p,hp⟩ hz
    rw [hevent.deriv_eq]
    exact hd p hp

theorem injective_closure_of_disk_side {U V : Set ℂ} (hV : IsOpen V)
    (hUV : closure U ⊆ V) {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F V)
    (hi : InjOn F U) (hm : F '' U = ball 0 1)
    (hside : ∀ z ∈ V, ‖F z‖ < 1 ↔ z ∈ U)
    (hd : ∀ p ∈ closure U, deriv F p ≠ 0) : InjOn F (closure U) := by
  intro p hp q hq he
  by_contra hpq
  obtain ⟨S,T,hS,hT,hpS,hqT,hST⟩ := t2_separation hpq
  have hpN : S ∩ V ∈ 𝓝 p := (hS.inter hV).mem_nhds ⟨hpS,hUV hp⟩
  have hqN : T ∩ V ∈ 𝓝 q := (hT.inter hV).mem_nhds ⟨hqT,hUV hq⟩
  have hpI : F '' (S ∩ V) ∈ 𝓝 (F p) := by
    rw [← (hF p (hUV hp)).hasStrictDerivAt.map_nhds_eq (hd p hp)]
    exact Filter.image_mem_map hpN
  have hqI : F '' (T ∩ V) ∈ 𝓝 (F p) := by
    rw [he, ← (hF q (hUV hq)).hasStrictDerivAt.map_nhds_eq (hd q hq)]
    exact Filter.image_mem_map hqN
  have hpCl : F p ∈ closure (ball (0 : ℂ) 1) := by
    rw [← hm]
    exact mem_closure_image (hF p (hUV hp)).continuousAt hp
  obtain ⟨w,hwI,hwD⟩ := mem_closure_iff_nhds.mp hpCl _ (inter_mem hpI hqI)
  obtain ⟨a,haS,haw⟩ := hwI.1
  obtain ⟨b,hbT,hbw⟩ := hwI.2
  have haU : a ∈ U := (hside a haS.2).mp (by rw [haw]; exact mem_ball_zero_iff.mp hwD)
  have hbU : b ∈ U := (hside b hbT.2).mp (by rw [hbw]; exact mem_ball_zero_iff.mp hwD)
  have hab : a = b := hi haU hbU (haw.trans hbw.symm)
  exact Set.disjoint_left.mp hST haS.1 (hab ▸ hbT.1)

theorem univalent_neighborhood_of_disk_side {U V : Set ℂ} (hV : IsOpen V)
    (hUV : closure U ⊆ V) (hUc : IsCompact (closure U))
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F V)
    (hi : InjOn F U) (hm : F '' U = ball 0 1)
    (hside : ∀ z ∈ V, ‖F z‖ < 1 ↔ z ∈ U)
    (hd : ∀ p ∈ closure U, deriv F p ≠ 0) :
    ∃ W, IsOpen W ∧ closure U ⊆ W ∧ W ⊆ V ∧
      InjOn F W ∧ AnalyticOnNhd ℂ F W ∧ F '' closure U = closedBall 0 1 := by
  have hic := injective_closure_of_disk_side hV hUV hF hi hm hside hd
  have hlocal : ∀ p ∈ closure U, ∃ S ∈ 𝓝 p, InjOn F S := by
    intro p hp
    let d := (hF p (hUV hp)).hasStrictDerivAt.hasStrictFDerivAt_equiv (hd p hp)
    exact ⟨(d.toOpenPartialHomeomorph F).source,
      (d.toOpenPartialHomeomorph F).open_source.mem_nhds d.mem_toOpenPartialHomeomorph_source,
      (d.toOpenPartialHomeomorph F).injOn⟩
  obtain ⟨W,hW,hUW,hiW⟩ := hic.exists_isOpen_superset hUc
    (fun p hp => (hF p (hUV hp)).continuousAt) hlocal
  refine ⟨W ∩ V,hW.inter hV,fun z hz => ⟨hUW hz,hUV hz⟩,inter_subset_right,
    hiW.mono inter_subset_left,hF.mono inter_subset_right,?_⟩
  apply Subset.antisymm
  · rintro w ⟨z,hz,rfl⟩
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0), ← hm]
    exact mem_closure_image (hF z (hUV hz)).continuousAt hz
  · have hc : IsClosed (F '' closure U) :=
      (hUc.image_of_continuousOn (hF.continuousOn.mono hUV)).isClosed
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    apply hc.closure_subset_iff.mpr
    rw [← hm]
    exact image_mono subset_closure

end Conformal

end DirectCrouzeix

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/ConformalCollar.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

open InnerProductSpace Real

structure AnalyticBoundaryChart (U : Set ℂ) (p : ℂ) where
  chart : OpenPartialHomeomorph ℂ ℂ
  zero_mem : 0 ∈ chart.source
  at_zero : chart 0 = p
  analytic : AnalyticOnNhd ℂ chart chart.source
  inverse_analytic : AnalyticOnNhd ℂ chart.symm chart.target
  inverse_derivative : deriv chart.symm p ≠ 0
  side : ∀ z ∈ chart.source, chart z ∈ U ↔ 0 < z.im

def HasAnalyticBoundary (U : Set ℂ) : Prop :=
  ∀ p ∈ frontier U, Nonempty (AnalyticBoundaryChart U p)

theorem local_riemann_extension {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) {p : ℂ} (hp : p ∉ U)
    (C : AnalyticBoundaryChart U p) :
    ∃ r > 0, ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (ball p (3*r)) ∧
      EqOn E f (ball p (3*r) ∩ U) ∧
      (∀ z ∈ ball p (3*r), ‖E z‖ < 1 ↔ z ∈ U) ∧ deriv E p ≠ 0 := by
  have hphia : C.chart 0 ≠ a := by rw [C.at_zero]; intro he; exact hp (he ▸ ha)
  have hcn := (C.analytic 0 C.zero_mem).continuousAt
  have hav : ∀ᶠ z in 𝓝 (0 : ℂ), C.chart z ≠ a :=
    hcn.eventually (isClosed_singleton.isOpen_compl.mem_nhds hphia)
  obtain ⟨R,hR,hRB⟩ : ∃ R > 0, closedBall (0 : ℂ) R ⊆
      C.chart.source ∩ {z | C.chart z ≠ a} :=
    nhds_basis_closedBall.mem_iff.mp
      (inter_mem (C.chart.open_source.mem_nhds C.zero_mem) hav)
  have hRU : ∀ z ∈ closedBall (0 : ℂ) R, 0 < z.im → C.chart z ∈ U :=
    fun z hz hi => (C.side z (hRB hz).1).mpr hi
  have hfa : AnalyticOnNhd ℂ f U := hf.holomorphic.analyticOnNhd hU
  have hfcomp : AnalyticOnNhd ℂ (f ∘ C.chart) (closedBall 0 R ∩ {z | 0 < z.im}) := by
    intro z hz
    exact (hfa _ (hRU z hz.1 hz.2)).comp (C.analytic z (hRB hz.1).1)
  have hncomp : ∀ z ∈ closedBall 0 R ∩ {z : ℂ | 0 < z.im}, (f ∘ C.chart) z ≠ 0 := by
    intro z hz he
    exact (hRB hz.1).2 (hf.injective (hRU z hz.1 hz.2) ha (he.trans hf.normalized.symm))
  have hbcomp : ∀ z ∈ closedBall 0 R ∩ {z : ℂ | 0 < z.im}, ‖(f ∘ C.chart) z‖ < 1 := by
    intro z hz
    exact mem_ball_zero_iff.mp (hf.disk (hRU z hz.1 hz.2))
  have hlcomp : ∀ z ∈ closedBall 0 R, z.im = 0 →
      Tendsto (fun w => ‖(f ∘ C.chart) w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 1) := by
    intro z hz hi
    have hzS := (hRB hz).1
    have hpU : C.chart z ∉ U := by
      rw [C.side z hzS, hi]
      exact lt_irrefl _
    apply (norm_tendsto_one_boundary hU hf hs hpU).comp
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(C.analytic z hzS).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [(nhdsWithin_le_nhds : 𝓝[{w : ℂ | 0 < w.im}] z ≤ 𝓝 z)
      (C.chart.open_source.mem_nhds hzS), self_mem_nhdsWithin] with w hwS hwIm
    exact (C.side w hwS).mpr hwIm
  obtain ⟨G,hG,hGe,hGreal,hGd,hGside⟩ :=
    holomorphic_reflection_modulus hR hfcomp hncomp hbcomp hlcomp
  have hpT : p ∈ C.chart.target := by
    simpa only [C.at_zero] using C.chart.map_source C.zero_mem
  have hInv : C.chart.symm p = 0 :=
    (congrArg C.chart.symm C.at_zero.symm).trans (C.chart.left_inv C.zero_mem)
  have hNear : {z : ℂ | z ∈ C.chart.target ∧ C.chart.symm z ∈ ball 0 R} ∈ 𝓝 p := by
    apply inter_mem (C.chart.open_target.mem_nhds hpT)
    have := (C.inverse_analytic p hpT).continuousAt.preimage_mem_nhds
      (ball_mem_nhds (C.chart.symm p) hR)
    change C.chart.symm ⁻¹' ball (0 : ℂ) R ∈ 𝓝 p
    simpa only [hInv] using this
  obtain ⟨S,hS,hSB⟩ := Metric.mem_nhds_iff.mp hNear
  let E : ℂ → ℂ := G ∘ C.chart.symm
  have hE : AnalyticOnNhd ℂ E (ball p S) := by
    intro z hz
    exact (hG _ (hSB hz).2).comp (C.inverse_analytic z (hSB hz).1)
  have hEs : ∀ z ∈ ball p S, ‖E z‖ < 1 ↔ z ∈ U := by
    intro z hz
    have ht := (hSB hz).1
    change ‖G (C.chart.symm z)‖ < 1 ↔ z ∈ U
    rw [hGside _ (hSB hz).2, ← C.side _ (C.chart.map_target ht), C.chart.right_inv ht]
  have hEe : EqOn E f (ball p S ∩ U) := by
    intro z hz
    have ht := (hSB hz.1).1
    have him : 0 < (C.chart.symm z).im := by
      apply (C.side _ (C.chart.map_target ht)).mp
      rw [C.chart.right_inv ht]
      exact hz.2
    change G (C.chart.symm z) = f z
    rw [hGe ⟨(hSB hz.1).2,him⟩]
    simp only [Function.comp_apply, C.chart.right_inv ht]
  have hEd : deriv E p ≠ 0 := by
    have hGc := (hG 0 (mem_ball_self hR)).differentiableAt.hasDerivAt
    have hiC := (C.inverse_analytic p hpT).differentiableAt.hasDerivAt
    have hGc' : HasDerivAt G (deriv G 0) (C.chart.symm p) := by
      simpa only [hInv] using hGc
    have hh := hGc'.comp p hiC
    change deriv (G ∘ C.chart.symm) p ≠ 0
    rw [hh.deriv]
    exact mul_ne_zero hGd C.inverse_derivative
  refine ⟨S/3,by positivity,E,?_,?_,?_,hEd⟩
  · simpa only [show 3*(S/3) = S by ring] using hE
  · simpa only [show 3*(S/3) = S by ring] using hEe
  · simpa only [show 3*(S/3) = S by ring] using hEs

theorem inverse_riemann_collar {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsCompact (closure U)) (hUB : HasAnalyticBoundary U)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) :
    ∃ R > 1, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 R) ∧ InjOn g (ball 0 R) ∧
      g '' ball 0 1 = U ∧ g '' closedBall 0 1 = closure U ∧ g 0 = a ∧
      (∀ z ∈ ball 0 R, deriv g z ≠ 0) := by
  have hloc : ∀ p ∈ closure U, ∃ r > 0, ∃ E : ℂ → ℂ,
      AnalyticOnNhd ℂ E (ball p (3*r)) ∧ EqOn E f (ball p (3*r) ∩ U) ∧
      (∀ z ∈ ball p (3*r), ‖E z‖ < 1 ↔ z ∈ U) ∧ deriv E p ≠ 0 := by
    intro p hp
    by_cases hpin : p ∈ U
    · obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU p hpin
      refine ⟨r/3,by positivity,f,?_,fun _ _ => rfl,?_,hf.derivative p hpin⟩
      · simpa only [show 3*(r/3)=r by ring] using
          (hf.holomorphic.analyticOnNhd hU).mono hrU
      · intro z hz
        have hzU : z ∈ U := hrU (by simpa only [show 3*(r/3)=r by ring] using hz)
        exact iff_of_true (mem_ball_zero_iff.mp (hf.disk hzU)) hzU
    · have hpB : p ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hp,hpin⟩
      obtain ⟨C⟩ := hUB p hpB
      exact local_riemann_extension hU ha hf hs hpin C
  obtain ⟨V,F,hV,hUV,hF,hFf,hside,hd⟩ := patch_boundary_germs hU hloc
  have hi : InjOn F U := by
    intro x hx y hy he
    apply hf.injective hx hy
    simpa only [hFf hx,hFf hy] using he
  have hm : F '' U = ball 0 1 := hFf.image_eq.trans hs
  obtain ⟨W,hW,hUW,hWV,hiW,hFW,hmW⟩ :=
    univalent_neighborhood_of_disk_side hV hUV hUc hF hi hm hside hd
  let Z := W ∩ interior {z | deriv F z ≠ 0}
  have hZ : IsOpen Z := hW.inter isOpen_interior
  have hUZ : closure U ⊆ Z := by
    intro z hz
    refine ⟨hUW hz,mem_interior_iff_mem_nhds.mpr ?_⟩
    exact ((hF z (hUV hz)).deriv.continuousAt).eventually
      (isClosed_singleton.isOpen_compl.mem_nhds (hd z hz))
  have hZF : AnalyticOnNhd ℂ F Z := hFW.mono inter_subset_left
  have hdZ : ∀ z ∈ Z, deriv F z ≠ 0 := fun z hz => interior_subset hz.2
  have hiZ : InjOn F Z := hiW.mono inter_subset_left
  have hImage : IsOpen (F '' Z) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨z,hz,rfl⟩
    rw [← (hZF z hz).hasStrictDerivAt.map_nhds_eq (hdZ z hz)]
    exact Filter.image_mem_map (hZ.mem_nhds hz)
  have hSmall : closedBall (0 : ℂ) 1 ⊆ F '' Z := by
    rw [← hmW]
    exact image_mono hUZ
  obtain ⟨δ,hδ,hδsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hImage hSmall
  rw [thickening_closedBall hδ (by norm_num : (0 : ℝ) ≤ 1)] at hδsub
  let R := δ + 1
  have hR : 1 < R := by dsimp [R]; linarith
  have hball : ball (0 : ℂ) R ⊆ F '' Z := hδsub
  let g := Function.invFunOn F Z
  have hgr : ∀ z ∈ F '' Z, F (g z) = z := fun z hz => Function.invFunOn_eq hz
  have hgl : ∀ z ∈ Z, g (F z) = z := fun z hz => hiZ.leftInvOn_invFunOn hz
  have hgm : ∀ z ∈ F '' Z, g z ∈ Z := fun z hz => Function.invFunOn_mem hz
  have hgder : ∀ z ∈ ball (0 : ℂ) R,
      HasStrictDerivAt g (deriv F (g z))⁻¹ z := by
    intro z hz
    have hzI := hball hz
    have hh := inverse_hasStrictDerivAt hZ hZF.differentiableOn hiZ (hgm z hzI) (hdZ _ (hgm z hzI))
    simpa only [g,hgr z hzI] using hh
  have hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) R) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    exact fun z hz => (hgder z hz).hasDerivAt.differentiableAt.differentiableWithinAt
  refine ⟨R,hR,g,hg,?_,?_,?_,?_,?_⟩
  · intro x hx y hy he
    calc
      x = F (g x) := (hgr x (hball hx)).symm
      _ = F (g y) := congrArg F he
      _ = y := hgr y (hball hy)
  · apply Subset.antisymm
    · rintro w ⟨z,hz,rfl⟩
      have hzR := ball_subset_ball hR.le hz
      have hzI := hball hzR
      apply (hside _ (hWV (hgm z hzI).1)).mp
      rw [hgr z hzI]
      exact mem_ball_zero_iff.mp hz
    · intro z hz
      refine ⟨F z,?_,hgl z (hUZ (subset_closure hz))⟩
      rw [← hm]
      exact mem_image_of_mem F hz
  · apply Subset.antisymm
    · rintro w ⟨z,hz,rfl⟩
      rw [← hmW] at hz
      obtain ⟨y,hy,rfl⟩ := hz
      simpa only [hgl y (hUZ hy)] using hy
    · intro z hz
      refine ⟨F z,?_,hgl z (hUZ hz)⟩
      rw [← hmW]
      exact mem_image_of_mem F hz
  · have haZ := hUZ (subset_closure ha)
    have hFa : F a = 0 := (hFf ha).trans hf.normalized
    simpa only [hFa] using hgl a haZ
  · intro z hz
    rw [(hgder z hz).hasDerivAt.deriv]
    exact inv_ne_zero (hdZ _ (hgm z (hball hz)))

theorem exists_riemann_collar {U : Set ℂ} (hU : IsOpen U)
    (hUs : IsSimplyConnected U) (hproper : U ≠ univ)
    (hUc : IsCompact (closure U)) (hUB : HasAnalyticBoundary U)
    {a : ℂ} (ha : a ∈ U) :
    ∃ R > 1, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 R) ∧ InjOn g (ball 0 R) ∧
      g '' ball 0 1 = U ∧ g '' closedBall 0 1 = closure U ∧ g 0 = a ∧
      (∀ z ∈ ball 0 R, deriv g z ≠ 0) := by
  obtain ⟨f,hf,hs⟩ := exists_riemannMap hU hUs hproper ha
  exact inverse_riemann_collar hU hUc hUB ha hf hs

end Conformal

end DirectCrouzeix

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/AnalyticCharts.lean
section
namespace OAI

universe u_133 u_134 u_135

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

theorem analytic_inverse_chart {E : Type u_133} {F : Type u_134} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {x : E} (ha : AnalyticAt ℂ f x) (e : E ≃L[ℂ] F)
    (hd : HasFDerivAt f e.toContinuousLinearMap x) :
    ∃ U : OpenPartialHomeomorph E F, (U : E → F) = f ∧ x ∈ U.source ∧
      AnalyticAt ℂ U.symm (f x) := by
  have hsd : HasStrictFDerivAt f e.toContinuousLinearMap x := by
    rw [← hd.fderiv]
    exact ha.hasStrictFDerivAt
  let U := hsd.toOpenPartialHomeomorph f
  have hU : (U : E → F) = f := hsd.toOpenPartialHomeomorph_coe
  have hx : x ∈ U.source := hsd.mem_toOpenPartialHomeomorph_source
  refine ⟨U,hU,hx,?_⟩
  obtain ⟨p,hp⟩ := ha
  have hc : p 1 = (continuousMultilinearCurryFin1 ℂ E F).symm e.toContinuousLinearMap := by
    apply (continuousMultilinearCurryFin1 ℂ E F).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hp.hasFDerivAt.unique hd
  have hpU : HasFPowerSeriesAt U p x := hU ▸ hp
  simpa only [hU] using (U.hasFPowerSeriesAt_symm hx hpU hc).analyticAt

def conjugatePair (z : ℂ × ℂ) : ℂ × ℂ := (conj z.1,conj z.2)

theorem conjugatePair_continuous : Continuous conjugatePair :=
  (Complex.continuous_conj.comp continuous_fst).prodMk (Complex.continuous_conj.comp continuous_snd)

@[simp] theorem conjugatePair_zero : conjugatePair 0 = 0 := by simp [conjugatePair]

theorem normalized_implicit_graph {F : ℂ × ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hF0 : F 0 = 1) {b : ℝ} (hb : 0 < b)
    (hd : HasFDerivAt F ((b:ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0)
    (hconj : ∀ z, F (conjugatePair z) = conj (F z)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ deriv g 0 = 0 ∧
      (∀ᶠ z in 𝓝 0, F (z,g z) = 1) ∧
      (∀ᶠ z in 𝓝 0, g (conj z) = conj (g z)) := by
  let H := fun z : ℂ × ℂ => (z.1,F z-1)
  have hH0 : H 0 = 0 := by simp [H,hF0]
  have hbC : (b:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  let e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := (ContinuousLinearEquiv.refl ℂ ℂ).prodCongr
    (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (b:ℂ) hbC))
  have hH : AnalyticAt ℂ H 0 := analyticAt_fst.prod (hF.sub analyticAt_const)
  have hHd : HasFDerivAt H e.toContinuousLinearMap 0 := by
    convert! (hasFDerivAt_fst (𝕜 := ℂ) (p := (0:ℂ × ℂ))).prodMk (hd.sub_const 1) using 1
    ext <;> simp [e]
  obtain ⟨U,hU,h0,hUi⟩ := analytic_inverse_chart hH e hHd
  rw [hH0] at hUi
  have hU0 : U 0 = 0 := by rw [hU]; exact hH0
  have hi0 : U.symm 0 = 0 := by simpa only [hU0] using U.left_inv h0
  have ht0 : (0:ℂ × ℂ) ∈ U.target := hU0 ▸ U.map_source h0
  let V := fun z : ℂ => U.symm (z,0)
  have hV : AnalyticAt ℂ V 0 := hUi.comp (f := fun z : ℂ => (z,0)) (analyticAt_id.prod analyticAt_const)
  have hV0 : V 0 = 0 := hi0
  let g := fun z => (V z).2
  have hg : AnalyticAt ℂ g 0 := analyticAt_snd.comp hV
  have hvT : ∀ᶠ z in 𝓝 (0:ℂ), (z,0) ∈ U.target :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (U.open_target.mem_nhds ht0)
  have hvEq : ∀ᶠ z in 𝓝 (0:ℂ), H (V z) = (z,0) := by
    filter_upwards [hvT] with z hz
    exact hU ▸ U.right_inv hz
  have hvfst : ∀ᶠ z in 𝓝 (0:ℂ), (V z).1 = z := by
    filter_upwards [hvEq] with z hz
    exact congrArg Prod.fst hz
  have heq : ∀ᶠ z in 𝓝 (0:ℂ), F (z,g z) = 1 := by
    filter_upwards [hvEq,hvfst] with z hz hzf
    have hs : F (V z)-1 = 0 := congrArg Prod.snd hz
    have hev : V z = (z,g z) := Prod.ext hzf rfl
    simpa only [hev,sub_eq_zero] using hs
  have hg0 : g 0 = 0 := congrArg Prod.snd hV0
  have hgd : deriv g 0 = 0 := by
    have hdcomp := (show HasFDerivAt F ((b:ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) (0,g 0) by simpa only [hg0,Prod.zero_eq_mk] using hd).comp 0 ((hasDerivAt_id (0:ℂ)).prodMk hg.differentiableAt.hasDerivAt).hasFDerivAt
    have hdconst : HasDerivAt (fun z => F (z,g z)) (b*deriv g 0) 0 := by
      convert! hdcomp.hasDerivAt using 1 ; simp [ContinuousLinearMap.comp_apply]
    have heder := hdconst.congr_of_eventuallyEq (show (fun _ : ℂ => (1:ℂ)) =ᶠ[𝓝 0] (fun z => F (z,g z)) from by filter_upwards [heq] with z hz; exact hz.symm)
    have hzero := heder.unique (hasDerivAt_const (0:ℂ) (1:ℂ))
    exact (mul_eq_zero.mp hzero).resolve_left hbC
  have hconjH (z : ℂ × ℂ) : H (conjugatePair z) = conjugatePair (H z) := by
    change (conj z.1,F (conjugatePair z)-1) = (conj z.1,conj (F z-1))
    rw [hconj]; simp
  have hvSC : ∀ᶠ z in 𝓝 (0:ℂ), conjugatePair (V z) ∈ U.source := by
    have hc : ContinuousAt (fun z => conjugatePair (V z)) 0 := conjugatePair_continuous.continuousAt.comp hV.continuousAt
    have he0 : conjugatePair (V 0) = 0 := by rw [hV0]; simp
    exact hc.preimage_mem_nhds (he0 ▸ U.open_source.mem_nhds h0)
  have htconj : ∀ᶠ z in 𝓝 (0:ℂ), (conj z,0) ∈ U.target := by
    have ht : Tendsto (conj : ℂ → ℂ) (𝓝 0) (𝓝 0) := by simpa using Complex.continuous_conj.tendsto (0:ℂ)
    exact ht.eventually hvT
  refine ⟨g,hg,hg0,hgd,heq,?_⟩
  filter_upwards [hvEq,hvSC,htconj] with z hz hzS hzT
  have he : V (conj z) = conjugatePair (V z) := by
    apply U.injOn (U.map_target hzT) hzS
    rw [hU]
    rw [hconjH,hz]
    simpa [conjugatePair] using (show H (U.symm (conj z,0)) = (conj z,0) from hU ▸ U.right_inv hzT)
  exact congrArg Prod.snd he

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem negative_vertical_level_side {f : ℂ → ℝ}
    (hf : ContDiffAt ℝ 1 f 0) (hd : fderiv ℝ f 0 Complex.I < 0)
    (hreal : ∀ᶠ x : ℝ in 𝓝 0, f (x:ℂ) = 1) :
    ∃ r > 0, ∀ z ∈ ball (0:ℂ) r, (f z < 1 ↔ 0 < z.im) ∧ (1 < f z ↔ z.im < 0) := by
  have he : ∀ᶠ z in 𝓝 (0:ℂ), DifferentiableAt ℝ f z ∧ fderiv ℝ f z Complex.I < 0 := by
    have hc : ContinuousAt (fun z => fderiv ℝ f z Complex.I) 0 :=
      (hf.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
    filter_upwards [hf.eventually (by norm_num),hc.eventually_lt continuousAt_const hd] with z hz hzn
    exact ⟨hz.differentiableAt (by norm_num),hzn⟩
  obtain ⟨d,hd0,hdB⟩ := Metric.mem_nhds_iff.mp he
  obtain ⟨e,he0,heB⟩ := Metric.mem_nhds_iff.mp hreal
  let r := min (d/3) e
  have hr : 0 < r := lt_min (by positivity) he0
  have hrd : 3*r ≤ d := by dsimp [r]; have := min_le_left (d/3) e; linarith
  have hre : r ≤ e := min_le_right _ _
  refine ⟨r,hr,?_⟩
  intro z hz
  have hzN : ‖z‖ < r := mem_ball_zero_iff.mp hz
  have hx : |z.re| < r := lt_of_le_of_lt (Complex.abs_re_le_norm z) hzN
  have hy : |z.im| < r := lt_of_le_of_lt (Complex.abs_im_le_norm z) hzN
  have hyI : z.im ∈ Ioo (-r) r := abs_lt.mp hy
  have h0I : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  let v := fun y : ℝ => (z.re:ℂ)+(y:ℂ)*Complex.I
  have hvB (y : ℝ) (hy : y ∈ Ioo (-r) r) : v y ∈ ball (0:ℂ) d := by
    rw [mem_ball_zero_iff]
    calc
      ‖v y‖ ≤ ‖(z.re:ℂ)‖+‖(y:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = |z.re|+|y| := by simp [Complex.norm_real,Real.norm_eq_abs]
      _ < r+r := add_lt_add hx (abs_lt.mpr hy)
      _ < d := by linarith
  have hvd (y : ℝ) : HasDerivAt v Complex.I y := by
    simpa [v] using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I |>.const_add (z.re:ℂ)
  have hder (y : ℝ) (hy : y ∈ Ioo (-r) r) :
      HasDerivAt (fun y => f (v y)) (fderiv ℝ f (v y) Complex.I) y :=
    (hdB (hvB y hy)).1.hasFDerivAt.comp_hasDerivAt y (hvd y)
  have hanti : StrictAntiOn (fun y => f (v y)) (Ioo (-r) r) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    · intro y hy
      exact (hder y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [(hder y (interior_subset hy)).deriv]
      exact (hdB (hvB y (interior_subset hy))).2
  have hbase : f (v 0) = 1 := by
    simpa [v] using heB (show z.re ∈ ball (0:ℝ) e from mem_ball_zero_iff.mpr (by simpa [Real.norm_eq_abs] using lt_of_lt_of_le hx hre))
  have hvz : v z.im = z := Complex.re_add_im z
  constructor
  · have hh := hanti.lt_iff_gt hyI h0I
    change (f (v z.im) < f (v 0) ↔ 0 < z.im) at hh
    rwa [hbase,hvz] at hh
  · have hh := hanti.lt_iff_gt h0I hyI
    change (f (v 0) < f (v z.im) ↔ z.im < 0) at hh
    rwa [hbase,hvz] at hh

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem analytic_complex_chart {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hd : deriv f 0 ≠ 0) {P : ℂ → Prop} (hP : ∀ᶠ z in 𝓝 0, P z) :
    ∃ U : OpenPartialHomeomorph ℂ ℂ, (U : ℂ → ℂ) = f ∧ 0 ∈ U.source ∧
      AnalyticOnNhd ℂ U U.source ∧ AnalyticOnNhd ℂ U.symm U.target ∧
      deriv U.symm (f 0) ≠ 0 ∧ (∀ z ∈ U.source, P z) := by
  let e : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv f 0) hd)
  have hed : HasFDerivAt f e.toContinuousLinearMap 0 := by
    convert! hf.differentiableAt.hasDerivAt.hasFDerivAt using 1
  obtain ⟨U,hU,h0,hi⟩ := analytic_inverse_chart hf e hed
  have he : ∀ᶠ z in 𝓝 (0:ℂ), AnalyticAt ℂ f z ∧ AnalyticAt ℂ U.symm (f z) ∧ P z := by
    filter_upwards [hf.eventually_analyticAt,hf.continuousAt.eventually hi.eventually_analyticAt,hP] with z hz hzi hzP
    exact ⟨hz,hzi,hzP⟩
  obtain ⟨r,hr,hrB⟩ := Metric.mem_nhds_iff.mp he
  let V := U.restr (ball 0 r)
  have hs : V.source = U.source ∩ ball 0 r := by simp [V,isOpen_ball.interior_eq]
  have ht : V.target = U.target ∩ U.symm ⁻¹' ball 0 r := by simp [V,isOpen_ball.interior_eq]
  have hV : (V : ℂ → ℂ) = f := by simpa [V] using hU
  have hVi : (V.symm : ℂ → ℂ) = U.symm := rfl
  have ht0 : f 0 ∈ U.target := hU ▸ U.map_source h0
  have hui0 : U.symm (f 0) = 0 := by simpa only [hU] using U.left_inv h0
  have hdi := U.hasDerivAt_symm ht0 hd (show HasDerivAt U (deriv f 0) (U.symm (f 0)) by
    rw [hui0,hU]; exact hf.differentiableAt.hasDerivAt)
  refine ⟨V,hV,?_,?_,?_,?_,?_⟩
  · rw [hs]; exact ⟨h0,mem_ball_self hr⟩
  · intro z hz
    rw [hV]
    exact (hrB ((hs ▸ hz).2)).1
  · intro z hz
    rw [hVi]
    have hzS := U.map_target ((ht ▸ hz).1)
    have hi := (hrB ((ht ▸ hz).2)).2.1
    rw [← hU,U.right_inv ((ht ▸ hz).1)] at hi
    exact hi
  · rw [hVi,hdi.deriv]
    exact inv_ne_zero hd
  · intro z hz
    exact (hrB ((hs ▸ hz).2)).2.2

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

variable {ι : Type u_135} [Fintype ι]

def expLevel (v : ι → ℂ) (b : ι → ℝ) (z : ℂ) : ℝ :=
  ∑ i, Real.exp (inner ℝ (v i) z+b i)

end DirectCrouzeix.Geometry

end

end

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/ExponentialLevels.lean
section
namespace OAI

universe u_135 u_136 u_137

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

variable {ι : Type u_135} [Fintype ι]

def expGradient (v : ι → ℂ) (b : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i, Real.exp (inner ℝ (v i) z+b i) • v i

theorem expLevel_contDiff (v : ι → ℂ) (b : ι → ℝ) : ContDiff ℝ ⊤ (expLevel v b) := by
  apply ContDiff.sum
  intro i hi
  exact ((innerSL ℝ (v i)).contDiff.add contDiff_const).exp

theorem expLevel_hasFDerivAt (v : ι → ℂ) (b : ι → ℝ) (z : ℂ) :
    HasFDerivAt (expLevel v b) (innerSL ℝ (expGradient v b z)) z := by
  have hh := HasFDerivAt.fun_sum (x := z) (u := Finset.univ) (fun i _ =>
    (((innerSL ℝ (v i)).hasFDerivAt).add_const (b i)).exp)
  convert! hh using 1
  ext w
  simp only [expGradient,innerSL_apply_apply,sum_inner,real_inner_smul_left,sum_apply,smul_apply,smul_eq_mul]

theorem expLevel_first_order (v : ι → ℂ) (b : ι → ℝ) (z w : ℂ) :
    expLevel v b z + inner ℝ (expGradient v b z) (w-z) ≤ expLevel v b w := by
  have hh (i : ι) :
      Real.exp (inner ℝ (v i) z+b i) + Real.exp (inner ℝ (v i) z+b i)*inner ℝ (v i) (w-z) ≤
        Real.exp (inner ℝ (v i) w+b i) := by
    have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (inner ℝ (v i) (w-z)))
      (Real.exp_nonneg (inner ℝ (v i) z+b i))
    rw [← Real.exp_add] at ht
    have he : inner ℝ (v i) z+b i+inner ℝ (v i) (w-z) = inner ℝ (v i) w+b i := by
      rw [inner_sub_right]; ring
    rw [he] at ht
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hh i)
  simpa only [expLevel,expGradient,sum_inner,real_inner_smul_left,Finset.sum_add_distrib] using hs

theorem expGradient_ne_zero (v : ι → ℂ) (b : ι → ℝ) {p a : ℂ}
    (hp : expLevel v b p = 1) (ha : expLevel v b a < 1) : expGradient v b p ≠ 0 := by
  intro he
  have hh := expLevel_first_order v b p a
  rw [he,inner_zero_left,hp,add_zero] at hh
  linarith

theorem expLevel_convex (v : ι → ℂ) (b : ι → ℝ) : ConvexOn ℝ univ (expLevel v b) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a c ha hc hac
  have hh (i : ι) := convexOn_exp.2 (show inner ℝ (v i) x+b i ∈ univ from mem_univ _)
    (show inner ℝ (v i) y+b i ∈ univ from mem_univ _) ha hc hac
  have he (i : ι) : inner ℝ (v i) (a • x+c • y)+b i =
      a*(inner ℝ (v i) x+b i)+c*(inner ℝ (v i) y+b i) := by
    simp only [inner_add_right,inner_smul_right]
    have hb := congrArg (fun u : ℝ => u*b i) hac
    nlinarith
  simp only [expLevel,he]
  simpa [smul_eq_mul,Finset.sum_add_distrib,Finset.mul_sum] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hh i)

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

variable {ι : Type u_136} [Fintype ι]

def expComplex (α β γ : ι → ℝ) (z : ℂ × ℂ) : ℂ :=
  ∑ i, Complex.exp ((γ i:ℂ)+(α i:ℂ)*z.1+(β i:ℂ)*z.2)

theorem expComplex_analytic (α β γ : ι → ℝ) (z : ℂ × ℂ) : AnalyticAt ℂ (expComplex α β γ) z := by
  apply Finset.analyticAt_fun_sum
  intro i hi
  exact ((analyticAt_const.add (analyticAt_const.mul analyticAt_fst)).add
    (analyticAt_const.mul analyticAt_snd)).cexp

theorem expComplex_zero (α β γ : ι → ℝ) : expComplex α β γ 0 = (∑ i, Real.exp (γ i):ℝ) := by
  simp [expComplex,Complex.ofReal_exp]

theorem expComplex_conj (α β γ : ι → ℝ) (z : ℂ × ℂ) :
    expComplex α β γ (conj z.1,conj z.2) = conj (expComplex α β γ z) := by
  simp only [expComplex,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem expComplex_real (α β γ : ι → ℝ) (x y : ℝ) :
    expComplex α β γ (x,y) = (∑ i, Real.exp (γ i+α i*x+β i*y):ℝ) := by
  simp [expComplex,Complex.ofReal_exp]

theorem expComplex_hasFDerivAt_zero (α β γ : ι → ℝ) :
    HasFDerivAt (expComplex α β γ)
      (((∑ i, Real.exp (γ i)*α i : ℝ):ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ +
       ((∑ i, Real.exp (γ i)*β i : ℝ):ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := by
  have hh := HasFDerivAt.fun_sum (x := (0:ℂ × ℂ)) (u := Finset.univ) (fun i _ =>
    (((hasFDerivAt_const (γ i:ℂ) (0:ℂ × ℂ)).add
      ((hasFDerivAt_fst (𝕜 := ℂ) (p := (0:ℂ × ℂ))).const_mul (α i:ℂ))).add
      ((hasFDerivAt_snd (𝕜 := ℂ) (p := (0:ℂ × ℂ))).const_mul (β i:ℂ))).cexp)
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro z
  simp [Complex.ofReal_exp,Finset.sum_mul,Finset.sum_add_distrib,mul_assoc]

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem closure_strict_level {f : ℂ → ℝ} (hc : Continuous f)
    (hv : ConvexOn ℝ univ f) {a : ℂ} (ha : f a < 1) :
    closure {z | f z < 1} = {z | f z ≤ 1} := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro z hz
      exact (show f z < 1 from hz).le
    · exact isClosed_le hc continuous_const
  · intro z hz
    let y := fun t : ℝ => (1-t) • z+t • a
    have hy : Continuous y := by fun_prop
    apply mem_closure_of_tendsto (b := 𝓝[>] (0:ℝ)) ((hy.tendsto' 0 z (by simp [y])).mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    have hh := hv.2 (mem_univ z) (mem_univ a) (sub_nonneg.mpr (le_of_lt ht.2)) (le_of_lt ht.1) (sub_add_cancel 1 t)
    change f (y t) ≤ (1-t)*f z+t*f a at hh
    change f (y t) < 1
    have h1 := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr (le_of_lt ht.2))
    have h2 := mul_lt_mul_of_pos_left ha ht.1
    nlinarith

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

variable {ι : Type u_137} [Fintype ι]

end DirectCrouzeix.Geometry

end

end

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/BoundaryParametrization.lean
section
namespace OAI

universe u_137

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

variable {ι : Type u_137} [Fintype ι]

theorem expLevel_boundary_parametrization (v : ι → ℂ) (b : ι → ℝ) {p a : ℂ}
    (hp : expLevel v b p = 1) (ha : expLevel v b a < 1) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 = p ∧ deriv H 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0, (expLevel v b (H z) < 1 ↔ 0 < z.im) ∧
        (1 < expLevel v b (H z) ↔ z.im < 0)) := by
  let q := expGradient v b p
  have hq : q ≠ 0 := expGradient_ne_zero v b hp ha
  let ξ := -Complex.I*q
  have hξ : ξ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hq
  have hIξ : Complex.I*ξ = q := by simp [ξ,← mul_assoc]
  have hqξ : inner ℝ q ξ = 0 := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply,ξ,Complex.mul_re,Complex.mul_im]
    ring
  let α := fun i => inner ℝ (v i) ξ
  let β := fun i => inner ℝ (v i) q
  let γ := fun i => inner ℝ (v i) p+b i
  have hα : ∑ i, Real.exp (γ i)*α i = 0 := by
    rw [← hqξ]
    dsimp only [q,expGradient]
    rw [sum_inner]
    simp only [real_inner_smul_left,α,γ]
  have hβ : ∑ i, Real.exp (γ i)*β i = ‖q‖^2 := by
    rw [← real_inner_self_eq_norm_sq,show q = expGradient v b p from rfl]
    conv_rhs => rw [expGradient]
    rw [sum_inner]
    simp only [real_inner_smul_left,β,γ,q,expGradient]
  have hF0 : expComplex α β γ 0 = 1 := by rw [expComplex_zero]; exact_mod_cast hp
  have hFd : HasFDerivAt (expComplex α β γ)
      (((‖q‖^2:ℝ):ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := by
    convert! expComplex_hasFDerivAt_zero α β γ using 1
    rw [hα,hβ]
    simp only [Complex.ofReal_zero]
    apply ContinuousLinearMap.ext
    intro z
    change _ = (0:ℂ)*z.1 + (‖q‖^2:ℝ)*z.2
    simp
  obtain ⟨g,hg,hg0,hgd,hge,hgc⟩ := normalized_implicit_graph (expComplex_analytic α β γ 0) hF0
    (sq_pos_of_pos (norm_pos_iff.mpr hq)) hFd (fun z => expComplex_conj α β γ z)
  let H := fun z : ℂ => p+ξ*(-z+Complex.I*g (-z))
  have hH0 : H 0 = p := by simp [H,hg0]
  have hHa : AnalyticAt ℂ H 0 := by
    exact analyticAt_const.add (analyticAt_const.mul (analyticAt_id.neg.add
      (analyticAt_const.mul ((show AnalyticAt ℂ g (-(0:ℂ)) from by simpa using hg).comp (f := fun z : ℂ => -z) analyticAt_id.neg))))
  have hHd : HasDerivAt H (-ξ) 0 := by
    have hdg : HasDerivAt (fun z : ℂ => g (-z)) 0 0 := by
      convert! (show HasDerivAt g (deriv g 0) (-(0:ℂ)) from by simpa using hg.differentiableAt.hasDerivAt).comp 0 (hasDerivAt_id (0:ℂ)).neg using 1
      simp [hgd]
    convert! (((hasDerivAt_id (0:ℂ)).neg.add (hdg.const_mul Complex.I)).const_mul ξ).const_add p using 1 ; simp
  have hreal : ∀ᶠ x : ℝ in 𝓝 0, expLevel v b (H (x:ℂ)) = 1 := by
    have ht : Tendsto (fun x : ℝ => -(x:ℂ)) (𝓝 0) (𝓝 0) := by convert! Complex.continuous_ofReal.neg.tendsto (0:ℝ) using 1 ; simp
    filter_upwards [ht.eventually hge,ht.eventually hgc] with x hx hxc
    have hi : (g (-(x:ℂ))).im = 0 := by
      simp only [map_neg,Complex.conj_ofReal] at hxc
      have hh := congrArg Complex.im hxc
      simp only [Complex.conj_im] at hh
      linarith
    have hgR : g (-(x:ℂ)) = ((g (-(x:ℂ))).re:ℂ) := by
      apply Complex.ext <;> simp [hi]
    have he : (expLevel v b (H (x:ℂ)):ℂ) = expComplex α β γ (-(x:ℂ),g (-(x:ℂ))) := by
      rw [hgR]
      rw [show -(x:ℂ) = ((-x:ℝ):ℂ) by simp,expComplex_real]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      have hHz : H (x:ℂ) = p+(-x) • ξ+(g (-(x:ℂ))).re • q := by
        dsimp only [H]
        rw [hgR]
        simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_re]
        rw [← hIξ]
        ring
      rw [hHz]
      simp only [inner_add_right,real_inner_smul_right,α,β,γ,Complex.ofReal_neg]
      ring
    rw [hx] at he
    exact_mod_cast he
  let f := fun z => expLevel v b (H z)
  have hf : ContDiffAt ℝ 1 f 0 :=
    ((expLevel_contDiff v b).of_le (by simp)).contDiffAt.comp 0 (hHa.contDiffAt.restrict_scalars ℝ)
  have hdf : fderiv ℝ f 0 Complex.I = -‖q‖^2 := by
    have hdφ : HasFDerivAt (expLevel v b) (innerSL ℝ q) (H 0) := by rw [hH0]; exact expLevel_hasFDerivAt v b p
    have hdcomp := hdφ.comp 0 (hHd.hasFDerivAt.restrictScalars ℝ)
    change fderiv ℝ (expLevel v b ∘ H) 0 Complex.I = _
    rw [hdcomp.fderiv]
    change inner ℝ q (Complex.I*(-ξ)) = _
    have he : Complex.I*(-ξ) = -q := by rw [mul_neg,hIξ]
    rw [he,inner_neg_right,real_inner_self_eq_norm_sq]
  obtain ⟨r,hr,hside⟩ := negative_vertical_level_side hf (by rw [hdf]; exact neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hq))) hreal
  refine ⟨H,hHa,hH0,?_,?_⟩
  · rw [hHd.deriv]; exact neg_ne_zero.mpr hξ
  · exact Filter.mem_of_superset (ball_mem_nhds (0:ℂ) hr) hside

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/InverseExterior.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

def inverseExterior (f : ℂ → ℝ) (a : ℂ) : Set ℂ := {w | w = 0 ∨ 1 < f (a+w⁻¹)}

@[simp] theorem zero_mem_inverseExterior (f : ℂ → ℝ) (a : ℂ) : 0 ∈ inverseExterior f a := Or.inl rfl

theorem mem_inverseExterior_iff {f : ℂ → ℝ} {a w : ℂ} (hw : w ≠ 0) :
    w ∈ inverseExterior f a ↔ 1 < f (a+w⁻¹) := or_iff_right hw

theorem inverseExterior_isOpen {f : ℂ → ℝ} (hf : Continuous f)
    (hc : IsCompact {z | f z ≤ 1}) (a : ℂ) : IsOpen (inverseExterior f a) := by
  obtain ⟨M,hM,hbound⟩ := hc.isBounded.exists_pos_norm_le
  rw [isOpen_iff_mem_nhds]
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    let r := (M+‖a‖+1)⁻¹
    have hr : 0 < r := inv_pos.mpr (by positivity)
    apply mem_of_superset (ball_mem_nhds (0:ℂ) hr)
    intro w hw
    by_cases hw0 : w = 0
    · exact Or.inl hw0
    apply Or.inr
    by_contra hn
    have hh := hbound (a+w⁻¹) (le_of_not_gt hn)
    have hnorm : ‖w⁻¹‖ ≤ M+‖a‖ := by
      calc
        ‖w⁻¹‖ = ‖(a+w⁻¹)-a‖ := by congr 1; abel
        _ ≤ ‖a+w⁻¹‖+‖a‖ := norm_sub_le _ _
        _ ≤ M+‖a‖ := add_le_add_left hh _
    have hrw : ‖w‖ < (M+‖a‖+1)⁻¹ := mem_ball_zero_iff.mp hw
    have hlarge : M+‖a‖+1 < ‖w‖⁻¹ := (lt_inv_comm₀ (norm_pos_iff.mpr hw0) (by positivity)).mp hrw
    rw [norm_inv] at hnorm
    linarith
  · have hc' : ContinuousAt (fun w : ℂ => f (a+w⁻¹)) w :=
      hf.continuousAt.comp (continuousAt_const.add (continuousAt_id.inv₀ hw0))
    have he : ∀ᶠ y in 𝓝 w, 1 < f (a+y⁻¹) := continuousAt_const.eventually_lt hc' ((mem_inverseExterior_iff hw0).mp hw)
    exact mem_of_superset he (fun y hy => Or.inr hy)

theorem inverseExterior_starConvex {f : ℂ → ℝ} (hf : ConvexOn ℝ univ f)
    {a : ℂ} (ha : f a < 1) : StarConvex ℝ 0 (inverseExterior f a) := by
  intro x hx t s ht hs hts
  simp only [smul_zero,zero_add]
  by_cases hs0 : s = 0
  · simp [hs0]
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxout := (mem_inverseExterior_iff hx0).mp hx
  apply Or.inr
  by_contra hn
  have hnew : f (a+(s • x)⁻¹) ≤ 1 := le_of_not_gt hn
  have hsC : (s:ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsum : (t:ℂ)+(s:ℂ)=1 := by exact_mod_cast hts
  have he : t • a+s • (a+(s • x)⁻¹) = a+x⁻¹ := by
    simp only [Complex.real_smul,mul_add]
    rw [mul_inv_rev]
    have hh : (s:ℂ)*((x⁻¹)*(s:ℂ)⁻¹) = x⁻¹ := by field_simp
    rw [hh]
    linear_combination a*hsum
  have hconv := hf.2 (mem_univ a) (mem_univ (a+(s • x)⁻¹)) ht hs hts
  rw [he] at hconv
  have h1 := mul_le_mul_of_nonneg_left (le_of_lt ha) ht
  have h2 := mul_le_mul_of_nonneg_left hnew hs
  dsimp only [smul_eq_mul] at hconv
  nlinarith

theorem inverseExterior_simplyConnected {f : ℂ → ℝ} (hf : ConvexOn ℝ univ f)
    {a : ℂ} (ha : f a < 1) : IsSimplyConnected (inverseExterior f a) := by
  let : ContractibleSpace (inverseExterior f a) :=
    (inverseExterior_starConvex hf ha).contractibleSpace ⟨0,zero_mem_inverseExterior f a⟩
  change SimplyConnectedSpace (inverseExterior f a)
  infer_instance

theorem inverseExterior_bounded {f : ℂ → ℝ} (hf : Continuous f)
    {a : ℂ} (ha : f a < 1) : ∃ L > 0, inverseExterior f a ⊆ closedBall 0 L := by
  have hnh : {z | f z < 1} ∈ 𝓝 a := (isOpen_lt hf continuous_const).mem_nhds ha
  obtain ⟨r,hr,hrB⟩ := Metric.mem_nhds_iff.mp hnh
  refine ⟨r⁻¹,inv_pos.mpr hr,?_⟩
  intro w hw
  rw [mem_closedBall_zero_iff]
  by_cases hw0 : w = 0
  · subst w; simp [le_of_lt (inv_pos.mpr hr)]
  by_contra hn
  have hwL : r⁻¹ < ‖w‖ := lt_of_not_ge hn
  have hninv : ‖w‖⁻¹ < r := (inv_lt_comm₀ hr (norm_pos_iff.mpr hw0)).mp hwL
  have hball : a+w⁻¹ ∈ ball a r := by simpa [dist_eq_norm,norm_inv] using hninv
  have hh : f (a+w⁻¹) < 1 := hrB hball
  have hout := (mem_inverseExterior_iff hw0).mp hw
  linarith

theorem inverseExterior_compact_closure {f : ℂ → ℝ} (hf : Continuous f)
    {a : ℂ} (ha : f a < 1) : IsCompact (closure (inverseExterior f a)) := by
  obtain ⟨L,hL,hB⟩ := inverseExterior_bounded hf ha
  exact (isCompact_closedBall (0:ℂ) L).of_isClosed_subset isClosed_closure
    (closure_minimal hB isClosed_closedBall)

theorem inverseExterior_proper {f : ℂ → ℝ} (hf : Continuous f)
    {a : ℂ} (ha : f a < 1) : inverseExterior f a ≠ univ := by
  obtain ⟨L,hL,hB⟩ := inverseExterior_bounded hf ha
  intro he
  have hh := hB (show ((L+1:ℝ):ℂ) ∈ inverseExterior f a from he ▸ mem_univ _)
  rw [mem_closedBall_zero_iff,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)] at hh
  linarith

theorem inverseExterior_frontier_level {f : ℂ → ℝ} (hf : Continuous f)
    (hc : IsCompact {z | f z ≤ 1}) {a w : ℂ}
    (hw : w ∈ frontier (inverseExterior f a)) : w ≠ 0 ∧ f (a+w⁻¹) = 1 := by
  have hU := inverseExterior_isOpen hf hc a
  have hw' : w ∈ closure (inverseExterior f a) ∧ w ∉ inverseExterior f a := by
    simpa only [frontier,hU.interior_eq,Set.mem_sdiff] using hw
  have hw0 : w ≠ 0 := by intro he; subst w; exact hw'.2 (zero_mem_inverseExterior f a)
  refine ⟨hw0,le_antisymm (le_of_not_gt (fun h => hw'.2 (Or.inr h))) ?_⟩
  by_contra hn
  have hl : f (a+w⁻¹) < 1 := lt_of_not_ge hn
  have hct : ContinuousAt (fun y : ℂ => f (a+y⁻¹)) w :=
    hf.continuousAt.comp (continuousAt_const.add (continuousAt_id.inv₀ hw0))
  have he : {y : ℂ | y ≠ 0 ∧ f (a+y⁻¹) < 1} ∈ 𝓝 w :=
    (continuousAt_id.eventually_ne hw0).and (hct.eventually_lt continuousAt_const hl)
  obtain ⟨y,hy,hyU⟩ := mem_closure_iff_nhds.mp hw'.1 _ he
  have hout := (mem_inverseExterior_iff hy.1).mp hyU
  linarith [hy.2]

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/ExteriorMapping.lean
section
namespace OAI

universe u_138 u_139

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

theorem exterior_laurent_form {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hinj : InjOn f (ball 0 R))
    (hf0 : f 0 = 0) (hd : ∀ u ∈ ball 0 R, deriv f u ≠ 0) (a : ℂ) :
    ∃ (c : ℂ) (g : ℂ → ℂ), c ≠ 0 ∧ AnalyticOnNhd ℂ g (ball 0 R) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → c*ζ+g ζ⁻¹ = a+(f ζ⁻¹)⁻¹) ∧
      InjOn (fun ζ => c*ζ+g ζ⁻¹) (Inv.inv ⁻¹' ball 0 R \ {0}) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → ζ⁻¹ ∈ ball 0 R → deriv (fun ζ => c*ζ+g ζ⁻¹) ζ ≠ 0) := by
  have h0 : (0:ℂ) ∈ ball 0 R := mem_ball_self hR
  let J := dslope f 0
  have hJ : AnalyticOnNhd ℂ J (ball 0 R) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds (0:ℂ) hR)).mpr hf.differentiableOn |>.analyticOnNhd isOpen_ball
  have hJ0 : J 0 = deriv f 0 := dslope_same _ _
  have hfn (u : ℂ) (hu : u ∈ ball 0 R) (hu0 : u ≠ 0) : f u ≠ 0 := by
    intro he
    exact hu0 (hinj hu h0 (he.trans hf0.symm))
  have hJn (u : ℂ) (hu : u ∈ ball 0 R) : J u ≠ 0 := by
    by_cases hu0 : u = 0
    · subst u; rw [hJ0]; exact hd 0 h0
    · dsimp only [J]
      rw [dslope_of_ne _ hu0]
      simp only [slope_def_field,hf0,sub_zero]
      exact div_ne_zero (hfn u hu hu0) hu0
  let F := fun u => (J u)⁻¹
  have hF : AnalyticOnNhd ℂ F (ball 0 R) := fun u hu => (hJ u hu).inv (hJn u hu)
  let c := F 0
  have hc : c ≠ 0 := inv_ne_zero (hJn 0 h0)
  let g := fun u => a+dslope F 0 u
  have hg : AnalyticOnNhd ℂ g (ball 0 R) := by
    have hs : AnalyticOnNhd ℂ (dslope F 0) (ball 0 R) :=
      (Complex.differentiableOn_dslope (ball_mem_nhds (0:ℂ) hR)).mpr hF.differentiableOn |>.analyticOnNhd isOpen_ball
    exact analyticOnNhd_const.add hs
  have he (ζ : ℂ) (hζ : ζ ≠ 0) : c*ζ+g ζ⁻¹ = a+(f ζ⁻¹)⁻¹ := by
    have hu : ζ⁻¹ ≠ 0 := inv_ne_zero hζ
    dsimp only [g]
    rw [dslope_of_ne _ hu,slope_def_field]
    dsimp only [F,J,c]
    rw [dslope_of_ne _ hu,slope_def_field,hf0]
    simp only [sub_zero,div_inv_eq_mul]
    field_simp
    ring
  have hder (ζ : ℂ) (hζ : ζ ≠ 0) (hu : ζ⁻¹ ∈ ball 0 R) :
      HasDerivAt (fun ζ => a+(f ζ⁻¹)⁻¹)
        (- (deriv f ζ⁻¹ * (-1/ζ^2))/(f ζ⁻¹)^2) ζ := by
    have hi : HasDerivAt (fun ζ : ℂ => ζ⁻¹) (-1/ζ^2) ζ := by
      convert! (hasDerivAt_id ζ).inv hζ using 1
    have hh := ((hf _ hu).differentiableAt.hasDerivAt.comp ζ hi).inv (hfn _ hu (inv_ne_zero hζ))
    convert! hh.const_add a using 1
  refine ⟨c,g,hc,hg,he,?_,?_⟩
  · intro ζ hζ η hη hh
    have hζ0 : ζ ≠ 0 := hζ.2
    have hη0 : η ≠ 0 := hη.2
    change c*ζ+g ζ⁻¹ = c*η+g η⁻¹ at hh
    rw [he ζ hζ0,he η hη0,add_right_inj] at hh
    exact inv_injective (hinj hζ.1 hη.1 (inv_injective hh))
  · intro ζ hζ hu
    have hev : (fun ζ => c*ζ+g ζ⁻¹) =ᶠ[𝓝 ζ] (fun ζ => a+(f ζ⁻¹)⁻¹) := by
      filter_upwards [continuousAt_id.eventually_ne hζ] with z hz
      exact he z hz
    rw [((hder ζ hζ hu).congr_of_eventuallyEq hev).deriv]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (hd _ hu)
      (div_ne_zero (by norm_num) (pow_ne_zero _ hζ)))) (pow_ne_zero _ (hfn _ hu (inv_ne_zero hζ)))

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem inverseExterior_analytic_boundary {ι : Type u_138} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | expLevel v b z ≤ 1})
    {a : ℂ} (ha : expLevel v b a < 1) :
    Conformal.HasAnalyticBoundary (inverseExterior (expLevel v b) a) := by
  intro w hw
  obtain ⟨hw0,hlevel⟩ := inverseExterior_frontier_level (expLevel_contDiff v b).continuous hc hw
  obtain ⟨H,hHa,hH0,hHd,hside⟩ := expLevel_boundary_parametrization v b hlevel ha
  let k := fun z : ℂ => (H (-z)-a)⁻¹
  have hpa : H 0-a ≠ 0 := by rw [hH0,add_sub_cancel_left]; exact inv_ne_zero hw0
  have hk0 : k 0 = w := by simp [k,hH0]
  have hHneg : AnalyticAt ℂ (fun z : ℂ => H (-z)) 0 := by
    exact (show AnalyticAt ℂ H (-(0:ℂ)) from by simpa using hHa).comp analyticAt_id.neg
  have hka : AnalyticAt ℂ k 0 := (hHneg.sub analyticAt_const).inv (by simpa using hpa)
  have hkder : HasDerivAt k (deriv H 0/(H 0-a)^2) 0 := by
    have hdn := (show HasDerivAt H (deriv H 0) (-(0:ℂ)) from by simpa using hHa.differentiableAt.hasDerivAt).comp 0 (hasDerivAt_id (0:ℂ)).neg
    convert! (hdn.sub_const a).inv (by simpa using hpa) using 1 ; simp
  have hkdn : deriv k 0 ≠ 0 := by rw [hkder.deriv]; exact div_ne_zero hHd (pow_ne_zero _ hpa)
  have hkP : ∀ᶠ z in 𝓝 (0:ℂ), k z ∈ inverseExterior (expLevel v b) a ↔ 0 < z.im := by
    have ht : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℂ)
    have hne : ∀ᶠ z in 𝓝 (0:ℂ), H (-z)-a ≠ 0 :=
      (hHneg.continuousAt.sub continuousAt_const).eventually_ne (by simpa using hpa)
    filter_upwards [ht.eventually hside,hne] with z hz hzne
    rw [mem_inverseExterior_iff (show k z ≠ 0 from inv_ne_zero hzne)]
    dsimp only [k]
    rw [inv_inv,add_sub_cancel]
    simpa only [Complex.neg_im,neg_lt_zero] using hz.2
  obtain ⟨C,hC,hC0,hCa,hCi,hCd,hCP⟩ := analytic_complex_chart hka hkdn hkP
  exact ⟨⟨C,hC0,by rw [hC,hk0],hCa,hCi,by rwa [hk0] at hCd,by simpa only [hC] using hCP⟩⟩

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem exists_expLevel_exterior {ι : Type u_139} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | expLevel v b z ≤ 1})
    {a : ℂ} (ha : expLevel v b a < 1) :
    ∃ R > 1, ∃ (c : ℂ) (g : ℂ → ℂ), c ≠ 0 ∧ AnalyticOnNhd ℂ g (ball 0 R) ∧
      InjOn (fun ζ => c*ζ+g ζ⁻¹) (Inv.inv ⁻¹' ball 0 R \ {0}) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → ζ⁻¹ ∈ ball 0 R → deriv (fun ζ => c*ζ+g ζ⁻¹) ζ ≠ 0) ∧
      (∀ ζ : ℂ, ‖ζ‖ = 1 → expLevel v b (c*ζ+g ζ⁻¹) = 1) ∧
      (∀ ζ : ℂ, 1 < ‖ζ‖ → 1 < expLevel v b (c*ζ+g ζ⁻¹)) := by
  let U := inverseExterior (expLevel v b) a
  have hct := (expLevel_contDiff v b).continuous
  have hU : IsOpen U := inverseExterior_isOpen hct hc a
  obtain ⟨R,hR,f,hfa,hfi,hopen,hclosed,hf0,hfd⟩ := Conformal.exists_riemann_collar hU
    (inverseExterior_simplyConnected (expLevel_convex v b) ha)
    (inverseExterior_proper hct ha) (inverseExterior_compact_closure hct ha)
    (inverseExterior_analytic_boundary v b hc ha) (zero_mem_inverseExterior _ a)
  obtain ⟨c,g,hc0,hg,he,hi,hd⟩ := exterior_laurent_form (by linarith : 0 < R) hfa hfi hf0 hfd a
  refine ⟨R,hR,c,g,hc0,hg,hi,hd,?_,?_⟩
  · intro ζ hζ
    have hζ0 : ζ ≠ 0 := by intro hh; norm_num [hh] at hζ
    have hη : ‖ζ⁻¹‖ = 1 := by simp [norm_inv,hζ]
    have hηR : ζ⁻¹ ∈ ball 0 R := mem_ball_zero_iff.mpr (by rw [hη]; exact hR)
    have hfu : f ζ⁻¹ ∈ frontier U := by
      rw [frontier,hU.interior_eq]
      refine ⟨?_,?_⟩
      · rw [← hclosed]
        exact mem_image_of_mem f (mem_closedBall_zero_iff.mpr (by rw [hη]))
      · intro hh
        rw [← hopen] at hh
        obtain ⟨z,hz,hze⟩ := hh
        have hzR := ball_subset_ball hR.le hz
        have hez : z = ζ⁻¹ := hfi hzR hηR hze
        have hzlt := mem_ball_zero_iff.mp hz
        rw [hez,hη] at hzlt
        exact lt_irrefl _ hzlt
    obtain ⟨hfn,hfl⟩ := inverseExterior_frontier_level hct hc hfu
    rw [he ζ hζ0]
    exact hfl
  · intro ζ hζ
    have hζ0 : ζ ≠ 0 := by intro hh; norm_num [hh] at hζ
    have hηB : ζ⁻¹ ∈ ball 0 1 := by
      rw [mem_ball_zero_iff,norm_inv]
      exact inv_lt_one_of_one_lt₀ hζ
    have hηR := ball_subset_ball hR.le hηB
    have hfn : f ζ⁻¹ ≠ 0 := by
      intro hh
      have hη0 := hfi hηR (mem_ball_self (by linarith)) (hh.trans hf0.symm)
      exact (inv_ne_zero hζ0) hη0
    have hfu : f ζ⁻¹ ∈ U := by rw [← hopen]; exact mem_image_of_mem f hηB
    rw [he ζ hζ0]
    exact (mem_inverseExterior_iff hfn).mp hfu

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/SupportNets.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

theorem exists_axis_net {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : Finset ℂ, (∀ ν ∈ D, ‖ν‖ = 1) ∧ 1 ∈ D ∧ -1 ∈ D ∧
      Complex.I ∈ D ∧ -Complex.I ∈ D ∧
      (∀ ν : ℂ, ‖ν‖ = 1 → ∃ μ ∈ D, ‖ν-μ‖ < δ) := by
  classical
  obtain ⟨S,hS⟩ := (isCompact_sphere (0:ℂ) 1).elim_finite_subcover
    (fun ν : sphere (0:ℂ) 1 => ball (ν:ℂ) δ) (fun _ => isOpen_ball) (by
      intro ν hν
      exact mem_iUnion.mpr ⟨⟨ν,hν⟩,mem_ball_self hδ⟩)
  let D := S.image Subtype.val ∪ {1,-1,Complex.I,-Complex.I}
  refine ⟨D,?_,?_,?_,?_,?_,?_⟩
  · intro ν hν
    rcases Finset.mem_union.mp hν with hν | hν
    · obtain ⟨μ,hμ,rfl⟩ := Finset.mem_image.mp hν
      simpa only [mem_sphere,dist_zero_right] using μ.property
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hν
      rcases hν with rfl | rfl | rfl | rfl <;> simp
  · simp [D]
  · simp [D]
  · simp [D]
  · simp [D]
  · intro ν hν
    obtain ⟨μ,hμ,hνμ⟩ := mem_iUnion₂.mp (hS (by simpa only [mem_sphere,dist_zero_right] using hν))
    refine ⟨μ,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨μ,hμ,rfl⟩),?_⟩
    simpa [dist_eq_norm] using hνμ

def convexSupport (K : Set ℂ) (ν : ℂ) : ℝ := sSup ((fun z => inner ℝ ν z) '' K)

theorem convexSupport_attained {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) (ν : ℂ) :
    ∃ w ∈ K, inner ℝ ν w = convexSupport K ν := by
  exact (hK.image ((innerSL ℝ ν).continuous)).sSup_mem (hne.image _)

theorem le_convexSupport {K : Set ℂ} (hK : IsCompact K) {z : ℂ} (hz : z ∈ K) (ν : ℂ) :
    inner ℝ ν z ≤ convexSupport K ν := by
  apply le_csSup (hK.image ((innerSL ℝ ν).continuous)).bddAbove
  exact mem_image_of_mem _ hz

theorem convexSupport_le {K : Set ℂ} (hne : K.Nonempty) {M : ℝ}
    (hM : ∀ z ∈ K, ‖z‖ ≤ M) {ν : ℂ} (hν : ‖ν‖ = 1) : convexSupport K ν ≤ M := by
  apply csSup_le (hne.image _)
  rintro x ⟨z,hz,rfl⟩
  exact (real_inner_le_norm ν z).trans (by simpa only [hν,one_mul] using hM z hz)

theorem direction_net_distance {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) {D : Finset ℂ} {δ M L : ℝ} (hδ : 0 < δ)
    (hM : ∀ w ∈ K, ‖w‖ ≤ M)
    (hnet : ∀ ν : ℂ, ‖ν‖ = 1 → ∃ μ ∈ D, ‖ν-μ‖ < δ)
    {z : ℂ} (hz : ‖z‖ ≤ L)
    (hs : ∀ μ ∈ D, inner ℝ μ z ≤ convexSupport K μ+δ) :
    ∃ w ∈ K, ‖z-w‖ ≤ δ*(1+L+M) := by
  obtain ⟨w,hw,hwmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hK.isClosed.isComplete hconv z
  have hM0 : 0 ≤ M := (norm_nonneg w).trans (hM w hw)
  have hL0 : 0 ≤ L := (norm_nonneg z).trans hz
  refine ⟨w,hw,?_⟩
  by_cases he : z = w
  · rw [he,sub_self,norm_zero]
    positivity
  have hn : 0 < ‖z-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  let ν := (‖z-w‖⁻¹:ℝ) • (z-w)
  have hν : ‖ν‖ = 1 := by simp [ν,ne_of_gt hn]
  obtain ⟨μ,hμ,hνμ⟩ := hnet ν hν
  obtain ⟨u,hu,hsu⟩ := convexSupport_attained hK hne μ
  have hmin : inner ℝ ν (u-w) ≤ 0 := by
    have hh := (norm_eq_iInf_iff_real_inner_le_zero hconv hw).mp hwmin u hu
    dsimp only [ν]
    rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr hn)) hh
  have hzw : inner ℝ ν (z-w) = ‖z-w‖ := by
    dsimp only [ν]
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp
  have hmain : ‖z-w‖ ≤ inner ℝ ν (z-u) := by
    have heq : z-w = (z-u)+(u-w) := by abel
    rw [← hzw,heq,inner_add_right]
    linarith
  have hμbound : inner ℝ μ (z-u) ≤ δ := by
    rw [inner_sub_right,hsu]
    linarith [hs μ hμ]
  have hnorm : ‖z-u‖ ≤ L+M := (norm_sub_le z u).trans (add_le_add hz (hM u hu))
  have herror : inner ℝ (ν-μ) (z-u) ≤ δ*(L+M) := by
    calc
      inner ℝ (ν-μ) (z-u) ≤ ‖ν-μ‖*‖z-u‖ := real_inner_le_norm _ _
      _ ≤ δ*(L+M) := mul_le_mul (le_of_lt hνμ) hnorm (norm_nonneg _) (le_of_lt hδ)
  have heq : inner ℝ ν (z-u) = inner ℝ μ (z-u)+inner ℝ (ν-μ) (z-u) := by
    rw [inner_sub_left]; ring
  rw [heq] at hmain
  nlinarith

theorem axis_support_bound {K : Set ℂ} (hne : K.Nonempty) {M δ : ℝ}
    (hM : ∀ w ∈ K, ‖w‖ ≤ M) {D : Finset ℂ}
    (h1 : 1 ∈ D) (hm1 : -1 ∈ D) (hI : Complex.I ∈ D) (hmI : -Complex.I ∈ D)
    {z : ℂ} (hs : ∀ μ ∈ D, inner ℝ μ z ≤ convexSupport K μ+δ) :
    ‖z‖ ≤ 2*(M+δ) := by
  have hb (μ : ℂ) (hμ : μ ∈ D) (hμN : ‖μ‖ = 1) : inner ℝ μ z ≤ M+δ :=
    (hs μ hμ).trans (add_le_add_left (convexSupport_le hne hM hμN) δ)
  have hr := hb 1 h1 (by simp)
  have hrr := hb (-1) hm1 (by simp)
  have hi := hb Complex.I hI (by simp)
  have hir := hb (-Complex.I) hmI (by simp)
  simp only [real_inner_eq_re_inner ℂ,RCLike.inner_apply] at hr hrr hi hir
  simp at hr hrr hi hir
  have ha : |z.re| ≤ M+δ := abs_le.mpr ⟨by linarith,hr⟩
  have hb : |z.im| ≤ M+δ := abs_le.mpr ⟨by linarith,hi⟩
  calc
    ‖z‖ ≤ |z.re|+|z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 2*(M+δ) := by linarith

end DirectCrouzeix.Geometry

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/Convexity.lean
section
namespace OAI

universe u_140 u_141 u_142

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix.Geometry

theorem sphere_lift {E : Type u_140} {F : Type u_141} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F) (hker : L.ker ≠ ⊥)
    {x : E} (hx : ‖x‖ ≤ 1) : ∃ y : E, ‖y‖ = 1 ∧ L y = L x := by
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,norm_ne_zero_iff.mpr hv0]
  have hLw : L w = 0 := by simp [w,show L v = 0 from hv]
  let b := inner ℝ x w
  have hn : 0 ≤ b^2+1-‖x‖^2 := by nlinarith [sq_nonneg b,norm_nonneg x]
  let t := -b+Real.sqrt (b^2+1-‖x‖^2)
  have ht : t^2+2*b*t+‖x‖^2 = 1 := by
    have hs := Real.sq_sqrt hn
    dsimp [t]
    nlinarith
  refine ⟨x+t • w,?_,by simp [hLw]⟩
  have hsq : ‖x+t • w‖^2 = 1 := by
    rw [norm_add_sq_real,inner_smul_right,norm_smul,hw,mul_one,Real.norm_eq_abs,sq_abs]
    change ‖x‖^2+2*(t*b)+t^2 = 1
    nlinarith [ht]
  nlinarith [norm_nonneg (x+t • w)]

abbrev Three := EuclideanSpace ℝ (Fin 3)

def bloch (u v : ℂ) : Three :=
  WithLp.toLp 2 ![2*(conj u*v).re,2*(conj u*v).im,Complex.normSq u-Complex.normSq v]

theorem norm_sq_three (p : Three) : ‖p‖^2 = p 0^2+p 1^2+p 2^2 := by
  simp [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,add_assoc]

theorem norm_bloch {u v : ℂ} (h : Complex.normSq u+Complex.normSq v = 1) : ‖bloch u v‖ = 1 := by
  have hm : (conj u*v).re^2+(conj u*v).im^2 = Complex.normSq u*Complex.normSq v := by
    calc
      _ = Complex.normSq (conj u*v) := by simp [Complex.normSq_apply,pow_two]
      _ = _ := by rw [Complex.normSq_mul,Complex.normSq_conj]
  have hsq : ‖bloch u v‖^2 = 1 := by
    rw [norm_sq_three]
    change (2*(conj u*v).re)^2+(2*(conj u*v).im)^2+(Complex.normSq u-Complex.normSq v)^2 = 1
    nlinarith [hm]
  nlinarith [norm_nonneg (bloch u v)]

theorem bloch_surjective_sphere {p : Three} (hp : ‖p‖ = 1) :
    ∃ u v : ℂ, Complex.normSq u+Complex.normSq v = 1 ∧ bloch u v = p := by
  have hsq : p 0^2+p 1^2+p 2^2 = 1 := by rw [← norm_sq_three,hp]; norm_num
  have hz : -1 ≤ p 2 ∧ p 2 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (p 0),sq_nonneg (p 1)]
  by_cases hzero : 1+p 2 = 0
  · have h2 : p 2 = -1 := by linarith
    have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 1)]
    have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0)]
    refine ⟨0,1,by norm_num,?_⟩
    ext i
    fin_cases i <;> simp [bloch,h0,h1,h2]
  · let s := (1+p 2)/2
    have hs : 0 < s := by dsimp [s]; exact div_pos (lt_of_le_of_ne (by linarith) (Ne.symm hzero)) (by norm_num)
    let a := Real.sqrt s
    have ha : 0 < a := Real.sqrt_pos.mpr hs
    have ha0 : a ≠ 0 := ne_of_gt ha
    have ha2 : a^2 = s := Real.sq_sqrt hs.le
    let u : ℂ := a
    let v : ℂ := ⟨p 0/(2*a),p 1/(2*a)⟩
    have hu : Complex.normSq u = s := by simp [u,Complex.normSq_apply]; nlinarith [ha2]
    have hv : Complex.normSq v = 1-s := by
      dsimp [v]
      field_simp
      dsimp [s] at *
      nlinarith [hsq,ha2]
    have hw : conj u*v = (⟨p 0/2,p 1/2⟩ : ℂ) := by
      apply Complex.ext <;> simp [u,v,Complex.mul_re,Complex.mul_im] <;> field_simp
    refine ⟨u,v,by rw [hu,hv]; ring,?_⟩
    ext i
    fin_cases i <;> simp [bloch,hw,hu,hv,s] <;> ring

def threeLinear (c : Fin 3 → ℂ) : Three →ₗ[ℝ] ℂ where
  toFun p := ∑ i, (p i : ℂ)*c i
  map_add' p q := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' a p := by simp [Complex.real_smul,Finset.mul_sum,mul_assoc]

theorem threeLinear_ker_ne_bot (c : Fin 3 → ℂ) : (threeLinear c).ker ≠ ⊥ := by
  apply LinearMap.ker_ne_bot_of_finrank_lt
  simp [Complex.finrank_real_complex,finrank_euclideanSpace]

def twoForm (a b c d u v : ℂ) : ℂ :=
  Complex.normSq u * a + Complex.normSq v * d + (conj u*v)*b + (conj v*u)*c

theorem twoForm_bloch (a b c d u v : ℂ) (h : Complex.normSq u+Complex.normSq v = 1) :
    twoForm a b c d u v = (a+d)/2 +
      threeLinear ![(b+c)/2,Complex.I*(b-c)/2,(a-d)/2] (bloch u v) := by
  have hh : (Complex.normSq u : ℂ)+(Complex.normSq v : ℂ) = 1 := by exact_mod_cast h
  have hw : conj v*u = conj (conj u*v) := by simp [mul_comm]
  simp only [twoForm,threeLinear,LinearMap.coe_mk,AddHom.coe_mk]
  change _ = (a+d)/2 + (((2*(conj u*v).re : ℝ):ℂ)*((b+c)/2) +
    (((2*(conj u*v).im : ℝ):ℂ)*(Complex.I*(b-c)/2) +
      (((Complex.normSq u-Complex.normSq v : ℝ):ℂ)*((a-d)/2) + 0)))
  rw [hw]
  apply Complex.ext
  · simp [Complex.mul_re,Complex.mul_im]
    linear_combination ((a.re+d.re)/2)*h
  · simp [Complex.mul_re,Complex.mul_im]
    linear_combination ((a.im+d.im)/2)*h

theorem convex_twoForm (a b c d : ℂ) :
    Convex ℝ {z : ℂ | ∃ u v : ℂ, Complex.normSq u+Complex.normSq v = 1 ∧ twoForm a b c d u v = z} := by
  intro x hx y hy r s hr hs hrs
  obtain ⟨u,v,huv,rfl⟩ := hx
  obtain ⟨w,z,hwz,rfl⟩ := hy
  let L := threeLinear ![(b+c)/2,Complex.I*(b-c)/2,(a-d)/2]
  have hn : ‖r • bloch u v+s • bloch w z‖ ≤ 1 := by
    calc
      _ ≤ ‖r • bloch u v‖+‖s • bloch w z‖ := norm_add_le _ _
      _ = r+s := by rw [norm_smul,norm_smul,norm_bloch huv,norm_bloch hwz,
        Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hr,abs_of_nonneg hs]; ring
      _ = 1 := hrs
  obtain ⟨p,hp,hLp⟩ := sphere_lift L (threeLinear_ker_ne_bot _) hn
  obtain ⟨α,β,hαβ,rfl⟩ := bloch_surjective_sphere hp
  refine ⟨α,β,hαβ,?_⟩
  rw [twoForm_bloch a b c d α β hαβ,twoForm_bloch a b c d u v huv,twoForm_bloch a b c d w z hwz]
  change (a+d)/2+L (bloch α β) = _
  rw [hLp,map_add,map_smul,map_smul]
  simp only [smul_add]
  rw [add_add_add_comm (r • ((a+d)/2)) (r • L (bloch u v)),← add_smul,hrs,one_smul]

section Inner

variable {E : Type u_142} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem orthonormal_pair_norm_sq {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = 0) (u v : ℂ) :
    ‖u • x+v • y‖^2 = Complex.normSq u+Complex.normSq v := by
  rw [norm_add_sq (𝕜 := ℂ),inner_smul_left,inner_smul_right,hxy,mul_zero,mul_zero]
  simp only [map_zero,mul_zero,add_zero,norm_smul,hx,hy,mul_one,Complex.normSq_eq_norm_sq]

theorem twoForm_inner {x y : E} (T : E →ₗ[ℂ] E) (u v : ℂ) :
    inner ℂ (u • x+v • y) (T (u • x+v • y)) =
      twoForm (inner ℂ x (T x)) (inner ℂ x (T y)) (inner ℂ y (T x)) (inner ℂ y (T y)) u v := by
  simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    twoForm]
  have hu : (Complex.normSq u : ℂ) = conj u*u := by rw [Complex.conj_mul',Complex.normSq_eq_norm_sq,Complex.ofReal_pow]
  have hv : (Complex.normSq v : ℂ) = conj v*v := by rw [Complex.conj_mul',Complex.normSq_eq_norm_sq,Complex.ofReal_pow]
  rw [hu,hv]
  ring

theorem convex_quadratic_range (T : E →ₗ[ℂ] E) :
    Convex ℝ {z : ℂ | ∃ x : E, ‖x‖ = 1 ∧ inner ℂ x (T x) = z} := by
  intro z hz w hw r s hr hs hrs
  obtain ⟨x,hx,rfl⟩ := hz
  obtain ⟨y,hy,rfl⟩ := hw
  let a := inner ℂ x y
  let v := y-a • x
  have hvorth : inner ℂ x v = 0 := by
    simp [v,a,inner_self_eq_norm_sq_to_K,hx]
  by_cases hv0 : v = 0
  · have hey : y = a • x := sub_eq_zero.mp hv0
    have han : ‖a‖ = 1 := by simpa [hey,norm_smul,hx] using hy
    have heq : inner ℂ y (T y) = inner ℂ x (T x) := by
      rw [hey,map_smul,inner_smul_left,inner_smul_right,← mul_assoc,Complex.conj_mul',han]
      simp
    refine ⟨x,hx,?_⟩
    rw [heq,← add_smul,hrs,one_smul]
  · let b : ℂ := ‖v‖
    let e := b⁻¹ • v
    have hb : b ≠ 0 := by dsimp [b]; exact_mod_cast norm_ne_zero_iff.mpr hv0
    have he : ‖e‖ = 1 := norm_smul_inv_norm hv0
    have hxe : inner ℂ x e = 0 := by simp [e,hvorth]
    have hyeq : y = a • x+b • e := by
      simp only [e,smul_smul,mul_inv_cancel₀ hb,one_smul,v]
      abel
    have hab : Complex.normSq a+Complex.normSq b = 1 := by
      rw [← orthonormal_pair_norm_sq hx he hxe a b,← hyeq,hy]
      norm_num
    let A := inner ℂ x (T x)
    let B := inner ℂ x (T e)
    let C := inner ℂ e (T x)
    let D := inner ℂ e (T e)
    have hxF : ∃ u v : ℂ, Complex.normSq u+Complex.normSq v = 1 ∧ twoForm A B C D u v = inner ℂ x (T x) := by
      exact ⟨1,0,by norm_num,by simp [twoForm,A]⟩
    have hyF : ∃ u v : ℂ, Complex.normSq u+Complex.normSq v = 1 ∧ twoForm A B C D u v = inner ℂ y (T y) := by
      refine ⟨a,b,hab,?_⟩
      rw [hyeq,twoForm_inner]
    obtain ⟨u,v,huv,hform⟩ := convex_twoForm A B C D hxF hyF hr hs hrs
    refine ⟨u • x+v • e,?_,?_⟩
    · have hn := orthonormal_pair_norm_sq hx he hxe u v
      rw [huv] at hn
      nlinarith [norm_nonneg (u • x+v • e)]
    · rw [twoForm_inner]
      exact hform

end Inner

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/ExponentialSupport.lean
section
namespace OAI

universe u_143

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix.Geometry

theorem positive_parallel_of_complex_inner {G q : ℂ} (hG : G ≠ 0) (hq : q ≠ 0)
    (horth : inner ℝ G (Complex.I*q) = 0) (hpos : 0 ≤ inner ℝ G q) :
    ∃ t : ℝ, 0 < t ∧ q = t • G := by
  have him : (conj G*q).im = 0 := by
    rw [real_inner_eq_re_inner ℂ,RCLike.inner_apply] at horth
    change ((Complex.I*q)*conj G).re = 0 at horth
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.conj_re,Complex.conj_im] at horth ⊢
    nlinarith
  have hre : (conj G*q).re = inner ℝ G q := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply,mul_comm]
  have hnon : inner ℝ G q ≠ 0 := by
    intro hh
    have he : conj G*q = 0 := Complex.ext (by simpa [hre] using hh) (by simpa using him)
    exact mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hG) hq he
  have hp : 0 < inner ℝ G q := lt_of_le_of_ne hpos (Ne.symm hnon)
  let t := inner ℝ G q/‖G‖^2
  refine ⟨t,div_pos hp (sq_pos_of_pos (norm_pos_iff.mpr hG)),?_⟩
  have hprod : conj G*q = (inner ℝ G q:ℂ) := by
    apply Complex.ext <;> simp [hre,him]
  have hGG : conj G*G = ((‖G‖^2:ℝ):ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  apply mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr hG : conj G ≠ 0)
  rw [hprod,Complex.real_smul,mul_left_comm,hGG]
  dsimp only [t]
  rw [Complex.ofReal_div,Complex.ofReal_pow,div_mul_cancel₀ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hG)))]

theorem expLevel_holomorphic_support {ι : Type u_143} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) {a : ℂ} (ha : expLevel v b a < 1)
    {ψ : ℂ → ℂ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hd : HasDerivAt ψ (deriv ψ ζ) ζ) (hdn : deriv ψ ζ ≠ 0)
    (hcircle : ∀ η : ℂ, ‖η‖ = 1 → expLevel v b (ψ η) = 1)
    (hout : ∀ η : ℂ, 1 ≤ ‖η‖ → 1 ≤ expLevel v b (ψ η))
    {w : ℂ} (hw : expLevel v b w ≤ 1) :
    0 ≤ inner ℝ (ζ*deriv ψ ζ) (ψ ζ-w) := by
  let G := expGradient v b (ψ ζ)
  let q := ζ*deriv ψ ζ
  have hζ0 : ζ ≠ 0 := by intro hh; simp [hh] at hζ
  have hq : q ≠ 0 := mul_ne_zero hζ0 hdn
  have hlevel : expLevel v b (ψ ζ) = 1 := hcircle ζ hζ
  have hG : G ≠ 0 := expGradient_ne_zero v b hlevel ha
  have hφd : HasFDerivAt (expLevel v b) (innerSL ℝ G) (ψ ζ) := expLevel_hasFDerivAt v b (ψ ζ)
  have horth : inner ℝ G (Complex.I*q) = 0 := by
    let e := fun t : ℝ => ζ*Complex.exp ((t:ℂ)*Complex.I)
    have he0 : e 0 = ζ := by simp [e]
    have hed : HasDerivAt e (ζ*Complex.I) 0 := by
      have hi : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 0 := by
        simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using! (Complex.ofRealCLM.hasDerivAt (x := (0:ℝ)))
      convert! ((hi.mul_const Complex.I).cexp).const_mul ζ using 1 ; simp
    have hψd := (show HasDerivAt ψ (deriv ψ ζ) (e 0) from he0 ▸ hd).scomp 0 hed
    have hcomp := (show HasFDerivAt (expLevel v b) (innerSL ℝ G) (ψ (e 0)) from he0 ▸ hφd).comp_hasDerivAt 0 hψd
    have hc : (fun t : ℝ => expLevel v b (ψ (e t))) = fun _ => 1 := by
      funext t
      apply hcircle
      simp [e,hζ,Complex.norm_exp]
    have hv : deriv (fun t : ℝ => expLevel v b (ψ (e t))) 0 = 0 := by rw [hc]; simp
    have heval : inner ℝ G (Complex.I*q) = (innerSL ℝ G) ((ζ*Complex.I) • deriv ψ ζ) := by
      simp only [innerSL_apply_apply,smul_eq_mul,q]; congr 1; ring
    rw [heval,← hcomp.deriv]
    exact hv
  have hpos : 0 ≤ inner ℝ G q := by
    let r := fun t : ℝ => (t:ℂ)*ζ
    have hr1 : r 1 = ζ := by simp [r]
    have hrd : HasDerivAt r ζ 1 := by
      have hi : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 1 := by
        simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using! (Complex.ofRealCLM.hasDerivAt (x := (1:ℝ)))
      convert! hi.mul_const ζ using 1 ; simp
    have hψd := (show HasDerivAt ψ (deriv ψ ζ) (r 1) from hr1 ▸ hd).scomp 1 hrd
    have hcomp := (show HasFDerivAt (expLevel v b) (innerSL ℝ G) (ψ (r 1)) from hr1 ▸ hφd).comp_hasDerivAt 1 hψd
    have hmin : IsMinOn (fun t : ℝ => expLevel v b (ψ (r t))) (Ici 1) 1 := by
      intro t ht
      change expLevel v b (ψ (r 1)) ≤ expLevel v b (ψ (r t))
      rw [hr1,hlevel]
      apply hout
      have ht0 : 0 ≤ t := le_trans (by norm_num) ht
      simpa [r,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0,hζ] using ht
    have htan : (1:ℝ) ∈ posTangentConeAt (Ici 1) 1 := by
      apply mem_posTangentConeAt_of_segment_subset
      exact (convex_Ici (1:ℝ)).segment_subset (by norm_num) (by norm_num)
    have hh := hmin.localize.hasFDerivWithinAt_nonneg hcomp.hasFDerivAt.hasFDerivWithinAt htan
    simpa [q] using hh
  obtain ⟨t,ht,hqeq⟩ := positive_parallel_of_complex_inner hG hq horth hpos
  have hs := expLevel_first_order v b (ψ ζ) w
  rw [hlevel,show expGradient v b (ψ ζ) = G from rfl] at hs
  have hsupport : 0 ≤ inner ℝ G (ψ ζ-w) := by
    rw [inner_sub_right] at hs ⊢
    linarith
  change 0 ≤ inner ℝ q (ψ ζ-w)
  rw [hqeq,real_inner_smul_left]
  exact mul_nonneg (le_of_lt ht) hsupport

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/OuterApproximation.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix.Geometry

theorem exists_exponential_outer {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hv : Convex ℝ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (D : Finset ℂ) (v : D → ℂ) (b : D → ℝ),
      (∀ z ∈ K, expLevel v b z < 1) ∧
      IsCompact {z | expLevel v b z ≤ 1} ∧
      (∀ z, expLevel v b z ≤ 1 → ∃ w ∈ K, ‖z-w‖ < ε) := by
  classical
  obtain ⟨M,hM0,hM⟩ := hK.isBounded.exists_pos_norm_le
  let L := 2*(M+1)
  let C := 1+L+M
  have hC : 0 < C := by dsimp [C,L]; linarith
  let δ := min (1/2) (ε/(2*C))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδε : δ*C < ε := by
    have hh : δ ≤ ε/(2*C) := min_le_right _ _
    have hc := (le_div_iff₀ (by positivity : 0 < 2*C)).mp hh
    nlinarith
  obtain ⟨D,hD,h1,hm1,hI,hmI,hnet⟩ := exists_axis_net hδ
  let N : ℝ := Fintype.card D
  have hN : 0 ≤ N := by dsimp [N]; positivity
  let t := (N+1)/δ
  have ht : 0 < t := div_pos (by linarith) hδ
  have htδ : t*δ = N+1 := div_mul_cancel₀ _ (ne_of_gt hδ)
  let v : D → ℂ := fun ν => t • (ν:ℂ)
  let b : D → ℝ := fun ν => -t*(convexSupport K ν+δ)
  have he (z : ℂ) (ν : D) : inner ℝ (v ν) z+b ν = t*(inner ℝ (ν:ℂ) z-convexSupport K ν-δ) := by
    dsimp only [v,b]
    rw [real_inner_smul_left]
    ring
  have hsumlt : N*Real.exp (-t*δ) < 1 := by
    rw [neg_mul,htδ,Real.exp_neg,mul_inv_lt_iff₀ (Real.exp_pos _),one_mul]
    linarith [Real.add_one_le_exp (N+1)]
  have hinside (z : ℂ) (hz : z ∈ K) : expLevel v b z < 1 := by
    calc
      expLevel v b z ≤ ∑ _ν : D, Real.exp (-t*δ) := by
        apply Finset.sum_le_sum
        intro ν hν
        rw [he]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (le_convexSupport hK hz (ν:ℂ)) (le_of_lt ht)
        nlinarith
      _ = N*Real.exp (-t*δ) := by simp [N]
      _ < 1 := hsumlt
  have hsupport (z : ℂ) (hz : expLevel v b z ≤ 1) (ν : ℂ) (hν : ν ∈ D) :
      inner ℝ ν z ≤ convexSupport K ν+δ := by
    have hh : Real.exp (inner ℝ (v ⟨ν,hν⟩) z+b ⟨ν,hν⟩) ≤ expLevel v b z :=
      Finset.single_le_sum (f := fun i : D => Real.exp (inner ℝ (v i) z+b i))
        (fun i _ => Real.exp_nonneg _) (Finset.mem_univ (⟨ν,hν⟩ : D))
    have hex := (Real.exp_le_one_iff).mp (hh.trans hz)
    rw [he] at hex
    nlinarith
  have hbound (z : ℂ) (hz : expLevel v b z ≤ 1) : ‖z‖ ≤ L := by
    have hh := axis_support_bound hne hM h1 hm1 hI hmI (hsupport z hz)
    dsimp [L]
    linarith
  refine ⟨D,v,b,hinside,?_,?_⟩
  · apply (isCompact_closedBall (0:ℂ) L).of_isClosed_subset
    · exact isClosed_le (expLevel_contDiff v b).continuous continuous_const
    · intro z hz
      exact mem_closedBall_zero_iff.mpr (hbound z hz)
  · intro z hz
    obtain ⟨w,hw,hzw⟩ := direction_net_distance hK hne hv hδ hM hnet (hbound z hz) (hsupport z hz)
    exact ⟨w,hw,lt_of_le_of_lt hzw hδε⟩

end DirectCrouzeix.Geometry

namespace DirectCrouzeix

@[simp] theorem matrixPolynomialValue_coefficientPolynomial {m d : ℕ}
    (B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ) (z : ℂ) :
    matrixPolynomialValue z (coefficientPolynomial B) = polynomialValue B z := by
  simp only [coefficientPolynomial,map_sum,map_mul,map_pow,matrixPolynomialValue_C,
    matrixPolynomialValue_X,smul_pow,one_pow,Matrix.mul_smul,Matrix.mul_one,polynomialValue]

@[simp] theorem matrixPolynomialValue_smul {m : ℕ} (F : MatrixPolynomial m) (s z : ℂ) :
    matrixPolynomialValue z (s • F) = s • matrixPolynomialValue z F := by
  rw [← smul_one_smul (Matrix (Fin m) (Fin m) ℂ) s F,Polynomial.smul_eq_C_mul,
    map_mul,matrixPolynomialValue_C,Matrix.smul_mul,Matrix.one_mul]

@[simp] theorem tensorPolynomial_smul {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (F : MatrixPolynomial m) (s : ℂ) :
    tensorPolynomial A (s • F) = s • tensorPolynomial A F := by
  rw [← smul_one_smul (Matrix (Fin m) (Fin m) ℂ) s F,Polynomial.smul_eq_C_mul,
    map_mul,tensorPolynomial_C,Matrix.kronecker_smul,Matrix.one_kronecker_one,
    Matrix.smul_mul,Matrix.one_mul]

end DirectCrouzeix

namespace DirectCrouzeix

open Set Filter Metric

end DirectCrouzeix

end

end

end

end

end

end

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/DomainBound.lean
section
namespace OAI

universe u_144 u_145

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix

open Set Filter Metric

theorem expLevel_domain_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) {ι : Type u_144} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | Geometry.expLevel v b z ≤ 1})
    (hW : ∀ z ∈ numericalRange A, Geometry.expLevel v b z < 1)
    (F : MatrixPolynomial m)
    (hF : ∀ z, Geometry.expLevel v b z ≤ 1 → ‖matrixPolynomialValue z F‖ ≤ 1) :
    ‖tensorPolynomial A F‖ ≤ 2 := by
  obtain ⟨a,ha⟩ := numericalRange_nonempty hn A
  obtain ⟨R,hR,c,g,hc0,hg,hinj,hder,hcircle,hout⟩ :=
    Geometry.exists_expLevel_exterior v b hc (hW a ha)
  have hge (ζ : ℂ) (hζ : 1 ≤ ‖ζ‖) : 1 ≤ Geometry.expLevel v b (Faber.exterior c g ζ) := by
    rcases eq_or_lt_of_le hζ with he|hl
    · exact le_of_eq (hcircle ζ he.symm).symm
    · exact le_of_lt (hout ζ hl)
  have hs (t : Faber.Angle) (w : ℂ) (hw : Geometry.expLevel v b w ≤ 1) :
      0 ≤ (conj (Faber.boundaryNormal c g t)*(Faber.boundary c g t-w)).re := by
    have hdt := Faber.hasDerivAt_exterior hg c (Faber.unitPoint_ne_zero t) (Faber.unitPoint_inv_mem hR t)
    have hh := Geometry.expLevel_holomorphic_support v b (hW a ha) (Faber.unitPoint_norm t)
      hdt.differentiableAt.hasDerivAt (hder _ (Faber.unitPoint_ne_zero t) (Faber.unitPoint_inv_mem hR t)) hcircle hge hw
    have he : Faber.unitPoint t*deriv (Faber.exterior c g) (Faber.unitPoint t) = Faber.boundaryNormal c g t := by
      rw [hdt.deriv]; rfl
    rw [he,real_inner_eq_re_inner ℂ,RCLike.inner_apply] at hh
    change 0 ≤ ((Faber.exterior c g (Faber.unitPoint t)-w)*conj (Faber.boundaryNormal c g t)).re at hh
    simpa only [Faber.boundary,mul_comm] using hh
  apply exterior_collar_bound hn hm A hR hg hc0 hinj hder
  · intro t s
    exact hs t _ (le_of_eq (hcircle _ (Faber.unitPoint_norm s)))
  · intro ζ hζ hz
    have h1 := hge ζ hζ
    have h2 := hW _ hz
    linarith
  · intro t w hw
    exact hs t w (le_of_lt (hW w hw))
  · intro t
    exact hF _ (le_of_eq (hcircle _ (Faber.unitPoint_norm t)))

theorem expLevel_domain_bound_scaled {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) {ι : Type u_145} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | Geometry.expLevel v b z ≤ 1})
    (hW : ∀ z ∈ numericalRange A, Geometry.expLevel v b z < 1)
    (F : MatrixPolynomial m) {ρ : ℝ} (hρ : 0 < ρ)
    (hF : ∀ z, Geometry.expLevel v b z ≤ 1 → ‖matrixPolynomialValue z F‖ ≤ ρ) :
    ‖tensorPolynomial A F‖ ≤ 2*ρ := by
  have hb := expLevel_domain_bound hn hm A v b hc hW (((ρ⁻¹:ℝ):ℂ) • F) (by
    intro z hz
    rw [matrixPolynomialValue_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)]
    exact (mul_le_mul_of_nonneg_left (hF z hz) (le_of_lt (inv_pos.mpr hρ))).trans_eq (inv_mul_cancel₀ (ne_of_gt hρ)))
  rw [tensorPolynomial_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)] at hb
  have hh := mul_le_mul_of_nonneg_left hb (le_of_lt hρ)
  rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hρ),one_mul] at hh
  simpa only [mul_comm] using hh

end DirectCrouzeix

namespace DirectCrouzeix

open Set Metric

end DirectCrouzeix

end

end

end

end

end

end

end

end

end

end OAI
end

-- OAI/Analysis/DirectCrouzeix/CompleteBound.lean
section
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix

open Set Metric

theorem convex_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Convex ℝ (numericalRange A) :=
  Geometry.convex_quadratic_range (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).toLinearMap

theorem complete_crouzeix : UniversalBound 2 := by
  intro n m d hn hm A B
  let M := rangeMaximum A B
  have hM : 0 ≤ M := by
    obtain ⟨z,hz,he⟩ := rangeMaximum_attained hn A B
    rw [show M = ‖polynomialValue B z‖ from he.symm]
    exact norm_nonneg _
  apply le_of_forall_pos_le_add
  intro ε hε
  let ρ := M+ε/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hMρ : M < ρ := by dsimp [ρ]; linarith
  let V := {z : ℂ | ‖polynomialValue B z‖ < ρ}
  have hV : IsOpen V := isOpen_lt (continuous_polynomialValue B).norm continuous_const
  have hWV : numericalRange A ⊆ V := by
    intro z hz
    exact lt_of_le_of_lt (norm_polynomialValue_le_rangeMaximum A B hz) hMρ
  obtain ⟨δ,hδ,hδV⟩ := (isCompact_numericalRange A).exists_thickening_subset_open hV hWV
  obtain ⟨D,v,b,hW,hc,hnear⟩ := Geometry.exists_exponential_outer (isCompact_numericalRange A)
    (numericalRange_nonempty hn A) (convex_numericalRange A) hδ
  have hbound : ∀ z, Geometry.expLevel v b z ≤ 1 →
      ‖matrixPolynomialValue z (coefficientPolynomial B)‖ ≤ ρ := by
    intro z hz
    rw [matrixPolynomialValue_coefficientPolynomial]
    apply le_of_lt
    apply hδV
    obtain ⟨w,hw,hzw⟩ := hnear z hz
    exact mem_thickening_iff.mpr ⟨w,hw,by simpa only [dist_eq_norm] using hzw⟩
  have hh := expLevel_domain_bound_scaled hn hm A v b hc hW (coefficientPolynomial B) hρ hbound
  rw [tensorPolynomial_coefficientPolynomial] at hh
  calc
    ‖tensorEvaluation A B‖ ≤ 2*ρ := hh
    _ = 2*rangeMaximum A B+ε := by dsimp [ρ,M]; ring

end DirectCrouzeix

end

end

end

end

end

end

end

end

end

end OAI
end

-- Bridge.lean
section
open scoped Matrix.Norms.L2Operator Kronecker
open OAI.DirectCrouzeix

noncomputable def scalarReindex (n : ℕ) :
    Matrix (Fin n × Fin 1) (Fin n × Fin 1) ℂ ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodUnique (Fin n) (Fin 1)) with
    map_smul' := by intro r A; ext i j; rfl
    map_star' := by intro A; ext i j; rfl }

lemma scalar_transfer {C : ℝ} (hc : UniversalBound C) :
    OMA.S_wpc_crouzeix_conjecture.UniversalBound C := by
  intro n hn A p
  let B : Fin (p.natDegree + 1) → Matrix (Fin 1) (Fin 1) ℂ :=
    fun k => p.coeff k • 1
  have hp (z : ℂ) : polynomialValue B z = p.eval z • 1 := by
    simp only [polynomialValue, B, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => z ^ k * p.coeff k), Polynomial.eval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  have he : scalarReindex n (tensorEvaluation A B) = Polynomial.aeval A p := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    simp only [tensorEvaluation, map_sum]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    ext i j
    simp [scalarReindex, B, Matrix.reindexAlgEquiv, Matrix.reindex_apply,
      Matrix.kroneckerMap_apply, Algebra.algebraMap_eq_smul_one, mul_comm]
  have heNorm : ‖tensorEvaluation A B‖ = ‖Polynomial.aeval A p‖ := by
    rw [← he, StarAlgEquiv.norm_map]
  have h := hc n 1 p.natDegree hn (by omega) A B
  rw [heNorm] at h
  simpa only [rangeMaximum, hp, norm_smul, norm_one, mul_one, numericalRange,
    OMA.S_wpc_crouzeix_conjecture.numericalRange] using h

lemma scalar_sharpness (C : ℝ)
    (hc : OMA.S_wpc_crouzeix_conjecture.UniversalBound C) : 2 ≤ C := by
  have h := hc 2 (by omega) sharpnessMatrix Polynomial.X
  simp only [Polynomial.aeval_X, Polynomial.eval_X] at h
  have hlow : 2 ≤ ‖sharpnessMatrix‖ := by
    have hentry := norm_entry_le_l2_opNorm sharpnessMatrix 0 1
    simpa [sharpnessMatrix] using hentry
  have he : sSup ((fun z : ℂ => ‖z‖) '' numericalRange sharpnessMatrix) =
      rangeMaximum (d := 1) sharpnessMatrix sharpnessCoefficients := by
    simp [rangeMaximum, sharpness_polynomialValue, norm_smul]
  change ‖sharpnessMatrix‖ ≤ C * sSup ((fun z : ℂ => ‖z‖) '' numericalRange sharpnessMatrix) at h
  rw [he] at h
  have hupper := sharpness_rangeMaximum_le_one
  have hnonneg : 0 ≤ rangeMaximum (d := 1) sharpnessMatrix sharpnessCoefficients := by
    obtain ⟨z, hz, he⟩ := rangeMaximum_attained (by omega : 0 < 2)
      sharpnessMatrix (d := 1) sharpnessCoefficients
    rw [← he]
    exact norm_nonneg _
  have hC : 0 ≤ C := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hn) hnonneg
    linarith
  have := mul_le_mul_of_nonneg_left hupper hC
  linarith
end

theorem OMA.solution : type_of% @OMA.S_wpc_crouzeix_conjecture.main :=
  ⟨scalar_transfer OAI.DirectCrouzeix.complete_crouzeix, scalar_sharpness⟩
