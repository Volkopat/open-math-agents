import OMAReductions.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1
import Mathlib
/-!
# Proof of Green100.green_100.parts.ii.R1.H2.R1.H2.R1.H2.R1.H4
Thom's normalization theorem in the internal case (arXiv:2609.27795, Theorem 1.2):
if the relative commutants of a unitary tuple and of its extension are internal in a tracial
matrix ultraproduct, and each added unitary conjugates the first comm into itself,
then it conjugates that comm onto itself.
All Haar averages over unitary groups of finite-dimensional C*-algebras are replaced by exact
finite averages over explicit Heisenberg-Weyl unitary 1-designs.
Credit: @zzzfu411
-/
namespace OMA.Green100H4
open Filter Matrix
open Finset (sum_congr sum_eq_zero mem_univ sum_eq_single sum_comm univ sum_const sum_le_sum mem_filter card_univ sum_sub_distrib sum_insert sum_nonneg sum_filter_add_sum_filter_not induction_on sum_const_zero mem_image_of_mem sum_ite_eq single_le_sum sum_attach abs_sum_le_sum_abs)
open Real (sqrt sqrt_le_sqrt sq_sqrt sqrt_sq sqrt_pos sqrt_nonneg mul_self_sqrt sqrt_mul sqrt_div)
open Fintype (sum_prod_type card_fin)
open Complex (re_sum sub_re star_def exp zero_re ofReal_mul exp_add norm_real conj_ofReal ofReal_sub)
open Unitary (star_mul_self_of_mem mul_star_self_of_mem)
open EuclideanSpace (norm_sq_eq inner_eq_star_dotProduct)
open scoped Topology ComplexOrder BigOperators Matrix InnerProductSpace
noncomputable section
lemma mma {l m n o α : Type*} [Fintype m] [Fintype n] [NonUnitalSemiring α] (A : Matrix l m α) (B : Matrix m n α) (C : Matrix n o α) : A * B * C = A * (B * C) := Matrix.mul_assoc A B C
lemma m1m {m n α : Type*} [Fintype m] [DecidableEq m] [NonAssocSemiring α] (A : Matrix m n α) : (1 : Matrix m m α) * A = A := Matrix.one_mul A
lemma mm1 {m n α : Type*} [Fintype n] [DecidableEq n] [NonAssocSemiring α] (A : Matrix m n α) : A * (1 : Matrix n n α) = A := Matrix.mul_one A
lemma mms {l m n α : Type*} [Fintype m] [NonUnitalNonAssocRing α] (A : Matrix l m α) (B C : Matrix m n α) : A * (B - C) = A * B - A * C := Matrix.mul_sub A B C
lemma msm {l m n α : Type*} [Fintype m] [NonUnitalNonAssocRing α] (A B : Matrix l m α) (C : Matrix m n α) : (A - B) * C = A * C - B * C := Matrix.sub_mul A B C
lemma ctM {l m n α : Type*} [Fintype m] [NonUnitalSemiring α] [StarRing α] (A : Matrix l m α) (B : Matrix m n α) : (A * B)ᴴ = Bᴴ * Aᴴ := Matrix.conjTranspose_mul A B
lemma ctct {m n α : Type*} [InvolutiveStar α] (A : Matrix m n α) : Aᴴᴴ = A := Matrix.conjTranspose_conjTranspose A
lemma ctA {m n α : Type*} [Star α] (A : Matrix m n α) (i : n) (j : m) : Aᴴ i j = star (A j i) := rfl
lemma ctS {m n α : Type*} [AddGroup α] [StarAddMonoid α] (A B : Matrix m n α) : (A - B)ᴴ = Aᴴ - Bᴴ := Matrix.conjTranspose_sub A B
/- ### 1. Hilbert-Schmidt norm, operator norm, and spectral calculus -/
section BasicHS
variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
abbrev CLM [DecidableEq n] (A : Matrix n n ℂ) :
  EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
 toEuclideanCLM (n := n) (𝕜 := ℂ) A
def hsSq (A : Matrix m n ℂ) : ℝ :=
 ∑ i : m, ∑ j : n, ‖A i j‖ ^ 2
def hsN (A : Matrix m n ℂ) : ℝ :=
 sqrt (hsSq A)
def m2e : Matrix m n ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (m × n) where
 toFun A := WithLp.toLp 2 (fun p : m × n => A p.1 p.2)
 invFun v i j := v.ofLp (i, j)
 left_inv A := by ext i j; rfl
 right_inv v := by ext ⟨i, j⟩; rfl
 map_add' A B := by ext ⟨i, j⟩; rfl
 map_smul' c A := by ext ⟨i, j⟩; rfl
lemma hsSq_nonneg (A : Matrix m n ℂ) : 0 ≤ hsSq A :=
 sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
lemma hsN_nn (A : Matrix m n ℂ) : 0 ≤ hsN A :=
 sqrt_nonneg _
lemma hsNorm_sq (A : Matrix m n ℂ) : hsN A ^ 2 = hsSq A :=
 sq_sqrt (hsSq_nonneg A)
lemma norm_matToEucl_sq (A : Matrix m n ℂ) : ‖m2e A‖ ^ 2 = hsSq A := by
 rw [norm_sq_eq, hsSq, sum_prod_type]
 rfl
lemma norm_matToEucl (A : Matrix m n ℂ) : ‖m2e A‖ = hsN A := by
 rw [hsN, ← norm_matToEucl_sq, sqrt_sq (norm_nonneg _)]
lemma inner_matToEucl (A B : Matrix m n ℂ) :
  ⟪m2e A, m2e B⟫_ℂ = (Aᴴ * B).trace := by
 rw [inner_eq_star_dotProduct, dotProduct, sum_prod_type]
 rw [Matrix.trace, sum_comm]
 refine sum_congr rfl fun j _ => ?_
 rw [Matrix.diag_apply, mul_apply]
 refine sum_congr rfl fun i _ => ?_
 change (m2e B).ofLp (i, j) * (starRingEnd ℂ) ((m2e A).ofLp (i, j)) =
  (Aᴴ) j i * B i j
 rw [ctA, mul_comm]
 rfl
lemma hsSq_trC (A : Matrix m n ℂ) :
  ((hsSq A : ℝ) : ℂ) = (Aᴴ * A).trace := by
 rw [← inner_matToEucl, inner_self_eq_norm_sq_to_K, norm_matToEucl, ← hsNorm_sq]
 simp
lemma hsSq_tr (A : Matrix m n ℂ) :
  hsSq A = ((Aᴴ * A).trace).re := by
 have h := congrArg Complex.re (hsSq_trC A)
 simpa using h
lemma hsSq_eq_zero_iff (A : Matrix m n ℂ) : hsSq A = 0 ↔ A = 0 := by
 rw [← norm_matToEucl_sq, sq_eq_zero_iff, norm_eq_zero,
  LinearEquiv.map_eq_zero_iff]
lemma hsN_add (A B : Matrix m n ℂ) : hsN (A + B) ≤ hsN A + hsN B := by
 simp only [← norm_matToEucl, map_add]
 exact norm_add_le _ _
lemma hsN_sub (A B : Matrix m n ℂ) : hsN (A - B) ≤ hsN A + hsN B := by
 simp only [← norm_matToEucl, map_sub]
 exact norm_sub_le _ _
lemma hsNorm_neg (A : Matrix m n ℂ) : hsN (-A) = hsN A := by
 simp only [← norm_matToEucl, map_neg, norm_neg]
lemma hsSq_neg (A : Matrix m n ℂ) : hsSq (-A) = hsSq A := by
 simp [hsSq]
lemma hsSq_ct (A : Matrix m n ℂ) : hsSq Aᴴ = hsSq A := by
 unfold hsSq
 rw [sum_comm]
 simp
lemma hsN_ct (A : Matrix m n ℂ) : hsN Aᴴ = hsN A := by
 simp [hsN, hsSq_ct]
lemma hsSq_smul (c : ℂ) (A : Matrix m n ℂ) : hsSq (c • A) = ‖c‖ ^ 2 * hsSq A := by
 rw [← norm_matToEucl_sq, ← norm_matToEucl_sq, map_smul, norm_smul, mul_pow]
lemma hsNorm_smul (c : ℂ) (A : Matrix m n ℂ) : hsN (c • A) = ‖c‖ * hsN A := by
 rw [← norm_matToEucl, ← norm_matToEucl, map_smul, norm_smul]
lemma hsSq_add_le (A B : Matrix m n ℂ) : hsSq (A + B) ≤ 2 * hsSq A + 2 * hsSq B := by
 have h := hsN_add A B
 have ha := hsN_nn A
 have hb := hsN_nn B
 have hab := hsN_nn (A + B)
 have hsq : hsN (A + B) ^ 2 ≤ (hsN A + hsN B) ^ 2 := by nlinarith
 rw [hsNorm_sq] at hsq
 nlinarith [sq_nonneg (hsN A - hsN B), hsNorm_sq A, hsNorm_sq B]
lemma hsSq_sub_le (A B : Matrix m n ℂ) : hsSq (A - B) ≤ 2 * hsSq A + 2 * hsSq B := by
 rw [sub_eq_add_neg, ← hsSq_neg B]
 exact hsSq_add_le A (-B)
lemma opNorm_conjTranspose [DecidableEq n] (A : Matrix n n ℂ) :
  ‖toEuclideanCLM (n := n) (𝕜 := ℂ) Aᴴ‖ =
   ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ := by
 rw [← star_eq_conjTranspose, map_star]
 exact norm_star (toEuclideanCLM (n := n) (𝕜 := ℂ) A)
lemma hsSq_mul_left_le [DecidableEq m] (Y : Matrix m m ℂ) (A : Matrix m n ℂ) :
  hsSq (Y * A) ≤ ‖toEuclideanCLM (n := m) (𝕜 := ℂ) Y‖ ^ 2 * hsSq A := by
 unfold hsSq
 rw [sum_comm, sum_comm (f := fun i j => ‖A i j‖ ^ 2), Finset.mul_sum]
 refine sum_le_sum fun j _ => ?_
 have h1 := (toEuclideanCLM (n := m) (𝕜 := ℂ) Y).le_opNorm
  (WithLp.toLp 2 (fun i => A i j))
 have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
 rw [mul_pow, norm_sq_eq, norm_sq_eq] at h2
 simpa [mul_apply, mulVec, dotProduct] using h2
lemma hsSq_mul_right_le [DecidableEq n] (A : Matrix m n ℂ) (Y : Matrix n n ℂ) :
  hsSq (A * Y) ≤ ‖toEuclideanCLM (n := n) (𝕜 := ℂ) Y‖ ^ 2 * hsSq A := by
 have h := hsSq_mul_left_le Yᴴ Aᴴ
 rw [← ctM, hsSq_ct, hsSq_ct,
  opNorm_conjTranspose] at h
 exact h
lemma hsN_mulL [DecidableEq m] (Y : Matrix m m ℂ) (A : Matrix m n ℂ) :
  hsN (Y * A) ≤ ‖toEuclideanCLM (n := m) (𝕜 := ℂ) Y‖ * hsN A := by
 have h := sqrt_le_sqrt (hsSq_mul_left_le Y A)
 rw [sqrt_mul (sq_nonneg _), sqrt_sq (norm_nonneg _)] at h
 exact h
lemma hsN_mulR [DecidableEq n] (A : Matrix m n ℂ) (Y : Matrix n n ℂ) :
  hsN (A * Y) ≤ ‖toEuclideanCLM (n := n) (𝕜 := ℂ) Y‖ * hsN A := by
 have h := sqrt_le_sqrt (hsSq_mul_right_le A Y)
 rw [sqrt_mul (sq_nonneg _), sqrt_sq (norm_nonneg _)] at h
 exact h
lemma hsSq_one [DecidableEq n] : hsSq (1 : Matrix n n ℂ) = Fintype.card n := by
 rw [hsSq_tr]
 simp [Matrix.trace]
lemma hsSq_le_card_mul_opNorm_sq [DecidableEq n] (Y : Matrix n n ℂ) :
  hsSq Y ≤ (Fintype.card n : ℝ) * ‖toEuclideanCLM (n := n) (𝕜 := ℂ) Y‖ ^ 2 := by
 have h := hsSq_mul_left_le Y (1 : Matrix n n ℂ)
 rw [mul_one, hsSq_one, mul_comm] at h
 exact h
lemma hsSq_isoL [DecidableEq n] (V : Matrix m n ℂ) (hV : Vᴴ * V = 1)
  (X : Matrix n k ℂ) : hsSq (V * X) = hsSq X := by
 rw [hsSq_tr, hsSq_tr, ctM, mma,
  ← mma Vᴴ, hV, m1m]
lemma hsSq_coisoR [DecidableEq m] (V : Matrix m n ℂ) (hV : V * Vᴴ = 1)
  (X : Matrix k m ℂ) : hsSq (X * V) = hsSq X := by
 rw [← hsSq_ct, ctM, hsSq_isoL Vᴴ (by simpa using hV),
  hsSq_ct]
lemma hsSq_proj_mul_le [DecidableEq n] (P : Matrix n n ℂ)
  (hPh : Pᴴ = P) (hPp : P * P = P) (X : Matrix n k ℂ) :
  hsSq (P * X) ≤ hsSq X := by
 have hQ : (1 - P)ᴴ * (1 - P) = 1 - P := by
  rw [ctS, conjTranspose_one, hPh,
   msm, mms, mms, m1m, m1m,
   mm1, hPp]
  abel
 have hsub : hsSq X - hsSq (P * X) = hsSq ((1 - P) * X) := by
  rw [hsSq_tr, hsSq_tr, hsSq_tr]
  have h1 : ((1 - P) * X)ᴴ * ((1 - P) * X) = Xᴴ * ((1 - P) * X) := by
   rw [ctM, mma, ← mma (1 - P)ᴴ, hQ]
  have h2 : (P * X)ᴴ * (P * X) = Xᴴ * (P * X) := by
   rw [ctM, mma, ← mma Pᴴ, hPh, hPp]
  rw [h1, h2, msm, m1m, mms, trace_sub, sub_re]
 linarith [hsSq_nonneg ((1 - P) * X)]
lemma hsSq_partialIsometry_mul_le [DecidableEq n] (W : Matrix m n ℂ)
  (hP : (Wᴴ * W) * (Wᴴ * W) = Wᴴ * W) (X : Matrix n k ℂ) :
  hsSq (W * X) ≤ hsSq X := by
 have hPh : (Wᴴ * W)ᴴ = Wᴴ * W := by simp
 have heq : hsSq (W * X) = hsSq ((Wᴴ * W) * X) := by
  rw [hsSq_tr, hsSq_tr]
  congr 1
  congr 1
  rw [ctM, ctM, hPh]
  calc
   Xᴴ * Wᴴ * (W * X) = Xᴴ * ((Wᴴ * W) * X) := by simp [mma]
   _ = Xᴴ * (((Wᴴ * W) * (Wᴴ * W)) * X) := by rw [hP]
   _ = Xᴴ * (Wᴴ * W) * ((Wᴴ * W) * X) := by simp [mma]
 rw [heq]
 exact hsSq_proj_mul_le (Wᴴ * W) hPh hP X
lemma hsSq_mul_partialIsometry_le [DecidableEq m] (W : Matrix m n ℂ)
  (hQ : (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ) (X : Matrix k m ℂ) :
  hsSq (X * W) ≤ hsSq X := by
 rw [← hsSq_ct, ctM]
 have hQ' : (Wᴴᴴ * Wᴴ) * (Wᴴᴴ * Wᴴ) = Wᴴᴴ * Wᴴ := by simpa using hQ
 exact (hsSq_partialIsometry_mul_le Wᴴ hQ' Xᴴ).trans_eq (hsSq_ct X)
lemma hsN_piL [DecidableEq n] (W : Matrix m n ℂ)
  (hP : (Wᴴ * W) * (Wᴴ * W) = Wᴴ * W) (X : Matrix n k ℂ) :
  hsN (W * X) ≤ hsN X :=
 sqrt_le_sqrt (hsSq_partialIsometry_mul_le W hP X)
lemma hsN_piR [DecidableEq m] (W : Matrix m n ℂ)
  (hQ : (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ) (X : Matrix k m ℂ) :
  hsN (X * W) ≤ hsN X :=
 sqrt_le_sqrt (hsSq_mul_partialIsometry_le W hQ X)
lemma opNorm_unitary_le' [DecidableEq n] {U : Matrix n n ℂ}
  (hU : U ∈ unitaryGroup n ℂ) :
  ‖toEuclideanCLM (n := n) (𝕜 := ℂ) U‖ ≤ 1 := by
 have h1 : star (toEuclideanCLM (n := n) (𝕜 := ℂ) U) *
   toEuclideanCLM (n := n) (𝕜 := ℂ) U = 1 := by
  rw [← map_star, ← map_mul, star_mul_self_of_mem hU, map_one]
 have h2 : ‖toEuclideanCLM (n := n) (𝕜 := ℂ) U‖ *
   ‖toEuclideanCLM (n := n) (𝕜 := ℂ) U‖ ≤ 1 := by
  rw [← CStarRing.norm_star_mul_self, h1]
  exact ContinuousLinearMap.norm_id_le
 nlinarith [norm_nonneg (toEuclideanCLM (n := n) (𝕜 := ℂ) U)]
lemma opNorm_mul_le' [DecidableEq n] (A B : Matrix n n ℂ) :
  ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (A * B)‖ ≤
   ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ * ‖toEuclideanCLM (n := n) (𝕜 := ℂ) B‖ := by
 rw [map_mul]
 exact norm_mul_le _ _
lemma opNorm_conj_unitary [DecidableEq n] {U : Matrix n n ℂ}
  (hU : U ∈ unitaryGroup n ℂ) (A : Matrix n n ℂ) :
  ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (Uᴴ * A * U)‖ =
   ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ := by
 apply le_antisymm
 ·
  calc
   ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (Uᴴ * A * U)‖
    ≤ ‖toEuclideanCLM (n := n) (𝕜 := ℂ) Uᴴ‖ *
     ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ *
     ‖toEuclideanCLM (n := n) (𝕜 := ℂ) U‖ := by
     refine (opNorm_mul_le' _ _).trans ?_
     gcongr
     exact opNorm_mul_le' _ _
   _ ≤ 1 * ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ * 1 := by
     gcongr
     · rw [opNorm_conjTranspose]; exact opNorm_unitary_le' hU
     · exact opNorm_unitary_le' hU
   _ = _ := by ring
 ·
  have hA : A = U * (Uᴴ * A * U) * Uᴴ := by
   have h1 : U * Uᴴ = 1 := mul_star_self_of_mem hU
   calc
    A = 1 * A * 1 := by simp
    _ = (U * Uᴴ) * A * (U * Uᴴ) := by rw [h1]
    _ = U * (Uᴴ * A * U) * Uᴴ := by noncomm_ring
  conv_lhs => rw [hA]
  calc
   ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (U * (Uᴴ * A * U) * Uᴴ)‖
    ≤ ‖toEuclideanCLM (n := n) (𝕜 := ℂ) U‖ *
     ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (Uᴴ * A * U)‖ *
     ‖toEuclideanCLM (n := n) (𝕜 := ℂ) Uᴴ‖ := by
     refine (opNorm_mul_le' _ _).trans ?_
     gcongr
     exact opNorm_mul_le' _ _
   _ ≤ 1 * ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (Uᴴ * A * U)‖ * 1 := by
     gcongr
     · exact opNorm_unitary_le' hU
     · rw [opNorm_conjTranspose]; exact opNorm_unitary_le' hU
   _ = _ := by ring
lemma opNorm_diagonal_le [DecidableEq n] (d : n → ℂ) {C : ℝ} (hC : 0 ≤ C)
  (hd : ∀ i, ‖d i‖ ≤ C) :
  ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.diagonal d)‖ ≤ C := by
 refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
 have hsq : ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.diagonal d) x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
  rw [mul_pow, norm_sq_eq, norm_sq_eq, Finset.mul_sum]
  refine sum_le_sum fun i _ => ?_
  simp only [ofLp_toEuclideanCLM, Matrix.mulVec_diagonal, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd i) 2) (sq_nonneg _)
 nlinarith [norm_nonneg (toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.diagonal d) x),
  mul_nonneg hC (norm_nonneg x)]
lemma opNorm_isHermitian_eigenvalues_le [DecidableEq n] {A : Matrix n n ℂ}
  (hA : A.IsHermitian) (i : n) :
  |hA.eigenvalues i| ≤ ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ := by
 have hv := (toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (hA.eigenvectorBasis i)
 have h1 : toEuclideanCLM (n := n) (𝕜 := ℂ) A (hA.eigenvectorBasis i) =
   (hA.eigenvalues i : ℂ) • (hA.eigenvectorBasis i) := by
  apply WithLp.ofLp_injective
  simpa [ofLp_toEuclideanCLM, RCLike.real_smul_eq_coe_smul] using
   hA.mulVec_eigenvectorBasis i
 rw [h1, norm_smul, norm_real, Real.norm_eq_abs, hA.eigenvectorBasis.orthonormal.1 i,
  mul_one, mul_one] at hv
 exact hv
/- ### 2. Polynomial realization of Hermitian functional calculus (Lagrange interpolation) -/
lemma aeval_diagonal [DecidableEq n] (d : n → ℂ) (p : Polynomial ℂ) :
  Polynomial.aeval (Matrix.diagonal d) p = Matrix.diagonal (fun i => p.eval (d i)) := by
 induction p using Polynomial.induction_on' with
 | add p q hp hq =>
  simp [map_add, hp, hq, Matrix.diagonal_add]
 | monomial k c =>
  simp only [Polynomial.aeval_monomial, Polynomial.eval_monomial]
  rw [Matrix.diagonal_pow]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Algebra.algebraMap_eq_smul_one]
  · simp [Matrix.diagonal_apply_ne _ hij, Algebra.algebraMap_eq_smul_one, Matrix.one_apply_ne hij]
lemma aeval_conjStarAlgAut [DecidableEq n] (U : unitaryGroup n ℂ)
  (A : Matrix n n ℂ) (p : Polynomial ℂ) :
  Polynomial.aeval (Unitary.conjStarAlgAut ℂ _ U A) p =
   Unitary.conjStarAlgAut ℂ _ U (Polynomial.aeval A p) := by
 induction p using Polynomial.induction_on' with
 | add p q hp hq => simp only [map_add, hp, hq]
 | monomial k c =>
  simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, map_mul, map_smul,
   map_one, map_pow]
lemma exists_poly_eval_on_finset (S : Finset ℝ) (f : ℝ → ℝ) :
  ∃ p : Polynomial ℂ, ∀ x ∈ S, p.eval (x : ℂ) = (f x : ℂ) := by
 classical
 let p : Polynomial ℂ :=
  ∑ x ∈ S, Polynomial.C (f x : ℂ) *
   ∏ y ∈ S.erase x, Polynomial.C (((x : ℂ) - (y : ℂ))⁻¹) * (Polynomial.X - Polynomial.C (y : ℂ))
 refine ⟨p, fun x hx => ?_⟩
 simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
  Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
 rw [sum_eq_single x]
 ·
  have hprod : ∏ y ∈ S.erase x, ((x : ℂ) - (y : ℂ))⁻¹ * ((x : ℂ) - (y : ℂ)) = 1 := by
   refine Finset.prod_eq_one fun y hy => ?_
   have hne : (x : ℂ) - (y : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    exact Complex.ofReal_injective.ne (Finset.ne_of_mem_erase hy).symm
   exact inv_mul_cancel₀ hne
  rw [hprod, mul_one]
 ·
  intro z hz hzx
  have hx_mem : x ∈ S.erase z := Finset.mem_erase.mpr ⟨hzx.symm, hx⟩
  have hzero : ∏ y ∈ S.erase z, ((z : ℂ) - (y : ℂ))⁻¹ * ((x : ℂ) - (y : ℂ)) = 0 :=
   Finset.prod_eq_zero hx_mem (by simp)
  rw [hzero, mul_zero]
 · intro h; exact absurd hx h
lemma exists_poly_cfc [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
  ∃ p : Polynomial ℂ, Polynomial.aeval A p = hA.cfc f := by
 classical
 obtain ⟨p, hp⟩ := exists_poly_eval_on_finset (univ.image hA.eigenvalues) f
 refine ⟨p, ?_⟩
 conv_lhs => rw [hA.spectral_theorem]
 rw [aeval_conjStarAlgAut, aeval_diagonal]
 unfold IsHermitian.cfc
 congr 1
 ext i j
 by_cases hij : i = j
 ·
  subst hij
  simpa [Function.comp_apply] using hp (hA.eigenvalues i) (mem_image_of_mem _ (mem_univ i))
 · simp [Matrix.diagonal_apply_ne _ hij]
lemma exists_poly_cfc_two [DecidableEq m] [DecidableEq n]
  {A : Matrix n n ℂ} (hA : A.IsHermitian) {B : Matrix m m ℂ} (hB : B.IsHermitian) (f : ℝ → ℝ) :
  ∃ p : Polynomial ℂ, Polynomial.aeval A p = hA.cfc f ∧ Polynomial.aeval B p = hB.cfc f := by
 classical
 let S : Finset ℝ := univ.image hA.eigenvalues ∪ univ.image hB.eigenvalues
 obtain ⟨p, hp⟩ := exists_poly_eval_on_finset S f
 refine ⟨p, ?_, ?_⟩
 ·
  conv_lhs => rw [hA.spectral_theorem]
  rw [aeval_conjStarAlgAut, aeval_diagonal]
  unfold IsHermitian.cfc
  congr 1; ext i j
  by_cases hij : i = j
  ·
   subst hij
   simpa [Function.comp_apply] using
    hp (hA.eigenvalues i) (Finset.mem_union_left _ (mem_image_of_mem _ (mem_univ i)))
  · simp [Matrix.diagonal_apply_ne _ hij]
 ·
  conv_lhs => rw [hB.spectral_theorem]
  rw [aeval_conjStarAlgAut, aeval_diagonal]
  unfold IsHermitian.cfc
  congr 1; ext i j
  by_cases hij : i = j
  ·
   subst hij
   simpa [Function.comp_apply] using
    hp (hB.eigenvalues i) (Finset.mem_union_right _ (mem_image_of_mem _ (mem_univ i)))
  · simp [Matrix.diagonal_apply_ne _ hij]
lemma aeval_intertwine [DecidableEq m] [DecidableEq n]
  (W : Matrix m n ℂ) (A : Matrix n n ℂ) (B : Matrix m m ℂ) (hW : W * A = B * W)
  (p : Polynomial ℂ) : W * Polynomial.aeval A p = Polynomial.aeval B p * W := by
 induction p using Polynomial.induction_on' with
 | add p q hp hq =>
  rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]
 | monomial k c =>
  simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
   Matrix.mul_smul, one_mul]
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
   rw [pow_succ, pow_succ, ← mma, ih, mma, hW, ← mma]
lemma cfc_intertwine [DecidableEq m] [DecidableEq n]
  (W : Matrix m n ℂ) {A : Matrix n n ℂ} (hA : A.IsHermitian)
  {B : Matrix m m ℂ} (hB : B.IsHermitian) (hW : W * A = B * W) (f : ℝ → ℝ) :
  W * hA.cfc f = hB.cfc f * W := by
 obtain ⟨p, hpA, hpB⟩ := exists_poly_cfc_two hA hB f
 rw [← hpA, ← hpB]
 exact aeval_intertwine W A B hW p
lemma cfc_commute [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
  (X : Matrix n n ℂ) (hX : X * A = A * X) (f : ℝ → ℝ) :
  X * hA.cfc f = hA.cfc f * X :=
 cfc_intertwine X hA hA hX f
lemma aeval_mem_starSubalgebra [DecidableEq n] {S : StarSubalgebra ℂ (Matrix n n ℂ)}
  {A : Matrix n n ℂ} (hAS : A ∈ S) (p : Polynomial ℂ) : Polynomial.aeval A p ∈ S := by
 induction p using Polynomial.induction_on' with
 | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
 | monomial k c =>
  rw [Polynomial.aeval_monomial]
  exact S.mul_mem (S.algebraMap_mem c) (S.pow_mem hAS k)
lemma cfc_mem_starSubalgebra [DecidableEq n] {S : StarSubalgebra ℂ (Matrix n n ℂ)}
  {A : Matrix n n ℂ} (hA : A.IsHermitian) (hAS : A ∈ S) (f : ℝ → ℝ) :
  hA.cfc f ∈ S := by
 obtain ⟨p, hp⟩ := exists_poly_cfc hA f
 rw [← hp]
 exact aeval_mem_starSubalgebra hAS p
lemma cfc_isHermitian [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
  (hA.cfc f).IsHermitian := by
 unfold IsHermitian.cfc IsHermitian
 rw [← star_eq_conjTranspose, ← map_star, star_eq_conjTranspose,
  Matrix.diagonal_conjTranspose]
 congr 1
 ext i j
 by_cases hij : i = j
 · subst hij; simp [Function.comp_apply]
 · simp [Matrix.diagonal_apply_ne _ hij]
lemma cfc_mul [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
  hA.cfc f * hA.cfc g = hA.cfc (fun t => f t * g t) := by
 unfold IsHermitian.cfc
 rw [← map_mul, Matrix.diagonal_mul_diagonal]
 congr 1
 ext i j
 by_cases hij : i = j
 · subst hij; simp [Function.comp_apply]
 · simp [Matrix.diagonal_apply_ne _ hij]
lemma cfc_add [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
  hA.cfc f + hA.cfc g = hA.cfc (fun t => f t + g t) := by
 unfold IsHermitian.cfc
 rw [← map_add, Matrix.diagonal_add]
 congr 1
 ext i j
 by_cases hij : i = j
 · subst hij; simp [Function.comp_apply]
 · simp [Matrix.diagonal_apply_ne _ hij]
lemma cfc_sub [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
  hA.cfc f - hA.cfc g = hA.cfc (fun t => f t - g t) := by
 unfold IsHermitian.cfc
 rw [← map_sub, Matrix.diagonal_sub]
 congr 1
 ext i j
 by_cases hij : i = j
 · subst hij; simp [Function.comp_apply]
 · simp [Matrix.diagonal_apply_ne _ hij]
lemma cfc_id [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
  hA.cfc id = A := by
 conv_rhs => rw [hA.spectral_theorem]
 rfl
lemma cfc_const [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) (c : ℝ) :
  hA.cfc (fun _ => c) = (c : ℂ) • (1 : Matrix n n ℂ) := by
 unfold IsHermitian.cfc
 have h1 : Matrix.diagonal (RCLike.ofReal ∘ (fun _ : ℝ => c) ∘ hA.eigenvalues) =
   (c : ℂ) • (1 : Matrix n n ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
 rw [h1, map_smul, map_one]
lemma cfc_one [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
  hA.cfc (fun _ => 1) = 1 := by
 rw [cfc_const]; simp
lemma cfc_congr [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) {f g : ℝ → ℝ}
  (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
  hA.cfc f = hA.cfc g := by
 unfold IsHermitian.cfc
 congr 1
 ext i j
 by_cases hij : i = j
 · subst hij; simp [h i]
 · simp [Matrix.diagonal_apply_ne _ hij]
lemma trace_cfc [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
  (hA.cfc f).trace = ∑ i : n, (f (hA.eigenvalues i) : ℂ) := by
 unfold IsHermitian.cfc
 rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
  Matrix.trace_diagonal]
 simp
lemma hsSq_cfc [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
  hsSq (hA.cfc f) = ∑ i : n, (f (hA.eigenvalues i)) ^ 2 := by
 rw [hsSq_tr, (cfc_isHermitian hA f).eq, cfc_mul, trace_cfc]
 simp [sq]
end BasicHS
/- ### 3. Commutant, conditional expectation, and finite-dimensional bicommutant theorem -/
section Bicommutant
variable {n : Type*} [Fintype n] [DecidableEq n]
def comm (A : StarSubalgebra ℂ (Matrix n n ℂ)) :
  StarSubalgebra ℂ (Matrix n n ℂ) where
 carrier := {X | ∀ a ∈ A, X * a = a * X}
 mul_mem' {X Y} hX hY a ha := by
  rw [mma, hY a ha, ← mma, hX a ha, mma]
 one_mem' a _ := by simp
 add_mem' {X Y} hX hY a ha := by rw [add_mul, mul_add, hX a ha, hY a ha]
 zero_mem' a _ := by simp
 algebraMap_mem' c a _ := by
  simp [Algebra.algebraMap_eq_smul_one]
 star_mem' {X} hX a ha := by
  have h := congrArg star (hX (star a) (star_mem ha))
  simpa [star_mul] using h.symm
lemma mem_commutant {A : StarSubalgebra ℂ (Matrix n n ℂ)} {X : Matrix n n ℂ} :
  X ∈ comm A ↔ ∀ a ∈ A, X * a = a * X := Iff.rfl
lemma le_commutant_commutant (A : StarSubalgebra ℂ (Matrix n n ℂ)) :
  A ≤ comm (comm A) :=
 fun _ ha _ hX => (hX _ ha).symm
lemma commutant_antitone {A B : StarSubalgebra ℂ (Matrix n n ℂ)} (h : A ≤ B) :
  comm B ≤ comm A :=
 fun _ hX a ha => hX a (h ha)
def subalgebraSubmodule (A : StarSubalgebra ℂ (Matrix n n ℂ)) :
  Submodule ℂ (EuclideanSpace ℂ (n × n)) :=
 A.toSubmodule.map m2e.toLinearMap
def cExp (A : StarSubalgebra ℂ (Matrix n n ℂ)) :
  Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
 m2e.symm.toLinearMap.comp
  (((subalgebraSubmodule A).starProjection.toLinearMap).comp m2e.toLinearMap)
lemma matToEucl_condExp (A : StarSubalgebra ℂ (Matrix n n ℂ)) (X : Matrix n n ℂ) :
  m2e (cExp A X) = (subalgebraSubmodule A).starProjection (m2e X) := by
 simp [cExp]
lemma condExp_mem (A : StarSubalgebra ℂ (Matrix n n ℂ)) (X : Matrix n n ℂ) :
  cExp A X ∈ A := by
 have hmem : m2e (cExp A X) ∈ subalgebraSubmodule A := by
  rw [matToEucl_condExp]
  exact (subalgebraSubmodule A).starProjection_apply_mem _
 rcases hmem with ⟨a, ha, hax⟩
 have : a = cExp A X := m2e.injective hax
 rwa [← this]
lemma condExp_eq_self {A : StarSubalgebra ℂ (Matrix n n ℂ)} {X : Matrix n n ℂ} (hX : X ∈ A) :
  cExp A X = X := by
 apply m2e.injective
 rw [matToEucl_condExp]
 exact (subalgebraSubmodule A).starProjection_eq_self_iff.mpr ⟨X, hX, rfl⟩
lemma condExp_inner_eq_zero (A : StarSubalgebra ℂ (Matrix n n ℂ)) (X : Matrix n n ℂ)
  {a : Matrix n n ℂ} (ha : a ∈ A) :
  ((X - cExp A X)ᴴ * a).trace = 0 := by
 rw [← inner_matToEucl, map_sub, matToEucl_condExp]
 exact (subalgebraSubmodule A).starProjection_inner_eq_zero (m2e X) (m2e a) ⟨a, ha, rfl⟩
lemma condExp_inner_eq (A : StarSubalgebra ℂ (Matrix n n ℂ)) (X : Matrix n n ℂ)
  {a : Matrix n n ℂ} (ha : a ∈ A) :
  ((cExp A X)ᴴ * a).trace = (Xᴴ * a).trace := by
 have h := condExp_inner_eq_zero A X ha
 rw [ctS, sub_mul, trace_sub, sub_eq_zero] at h
 exact h.symm
lemma hsSq_eq_hsSq_condExp_add (A : StarSubalgebra ℂ (Matrix n n ℂ)) (X : Matrix n n ℂ) :
  hsSq X = hsSq (cExp A X) + hsSq (X - cExp A X) := by
 have h1 : ((hsSq X : ℝ) : ℂ) =
   ((hsSq (cExp A X) : ℝ) : ℂ) + ((hsSq (X - cExp A X) : ℝ) : ℂ) := by
  rw [hsSq_trC, hsSq_trC, hsSq_trC]
  have hX : X = cExp A X + (X - cExp A X) := by abel
  conv_lhs => rw [hX]
  rw [conjTranspose_add, add_mul, mul_add, mul_add, trace_add, trace_add,
   trace_add]
  have h0 : ((X - cExp A X)ᴴ * cExp A X).trace = 0 :=
   condExp_inner_eq_zero A X (condExp_mem A X)
  have h0' : ((cExp A X)ᴴ * (X - cExp A X)).trace = 0 := by
   have hc := congrArg star h0
   rw [star_zero, ← trace_conjTranspose, ctM,
    ctct] at hc
   exact hc
  rw [h0, h0']
  ring
 exact_mod_cast h1
lemma hsSq_sub_condExp_le (A : StarSubalgebra ℂ (Matrix n n ℂ)) (X : Matrix n n ℂ)
  {a : Matrix n n ℂ} (ha : a ∈ A) :
  hsSq (X - cExp A X) ≤ hsSq (X - a) := by
 have h := hsSq_eq_hsSq_condExp_add A (X - a)
 rw [map_sub, condExp_eq_self ha] at h
 have heq : X - a - (cExp A X - a) = X - cExp A X := by abel
 rw [heq] at h
 linarith [hsSq_nonneg (cExp A X - a)]
lemma condExp_eq_of_mem_of_orthog (A : StarSubalgebra ℂ (Matrix n n ℂ))
  {X Y : Matrix n n ℂ} (hY : Y ∈ A) (horth : ∀ a ∈ A, ((X - Y)ᴴ * a).trace = 0) :
  cExp A X = Y := by
 have h1 := hsSq_sub_condExp_le A X hY
 have h2 : hsSq (X - cExp A X) = hsSq (X - Y) + hsSq (Y - cExp A X) := by
  have hdiff : ((X - Y)ᴴ * (Y - cExp A X)).trace = 0 :=
   horth (Y - cExp A X) (A.sub_mem hY (condExp_mem A X))
  have hdiff' : ((Y - cExp A X)ᴴ * (X - Y)).trace = 0 := by
   have hc := congrArg star hdiff
   rw [star_zero, ← trace_conjTranspose, ctM,
    ctct] at hc
   exact hc
  have hsub : ((hsSq (X - cExp A X) : ℝ) : ℂ) =
    ((hsSq (X - Y) : ℝ) : ℂ) + ((hsSq (Y - cExp A X) : ℝ) : ℂ) := by
   rw [hsSq_trC, hsSq_trC, hsSq_trC]
   have heq : X - cExp A X = (X - Y) + (Y - cExp A X) := by abel
   conv_lhs => rw [heq]
   rw [conjTranspose_add, add_mul, mul_add, mul_add, trace_add, trace_add,
    trace_add, hdiff, hdiff']
   ring
  exact_mod_cast hsub
 have hzero : hsSq (Y - cExp A X) = 0 := by linarith [hsSq_nonneg (Y - cExp A X)]
 exact (sub_eq_zero.mp ((hsSq_eq_zero_iff _).mp hzero)).symm
lemma condExp_star (A : StarSubalgebra ℂ (Matrix n n ℂ)) (X : Matrix n n ℂ) :
  cExp A Xᴴ = (cExp A X)ᴴ := by
 apply condExp_eq_of_mem_of_orthog A (star_mem (condExp_mem A X))
 intro a ha
 have h := condExp_inner_eq_zero A X (star_mem ha)
 rw [star_eq_conjTranspose] at h
 have h2 : ((Xᴴ - (cExp A X)ᴴ)ᴴ * a).trace =
   star (((X - cExp A X)ᴴ * aᴴ).trace) := by
  rw [← trace_conjTranspose, ctM, ctct,
   ctct, ctS, ctct,
   ctct, trace_mul_comm]
 rw [star_eq_conjTranspose, h2, h, star_zero]
lemma condExp_mul_left (A : StarSubalgebra ℂ (Matrix n n ℂ)) {a : Matrix n n ℂ} (ha : a ∈ A)
  (X : Matrix n n ℂ) : cExp A (a * X) = a * cExp A X := by
 apply condExp_eq_of_mem_of_orthog A (A.mul_mem ha (condExp_mem A X))
 intro b hb
 have h1 : ((a * X - a * cExp A X)ᴴ * b).trace =
   ((X - cExp A X)ᴴ * (aᴴ * b)).trace := by
  rw [← mul_sub, ctM, mma]
 rw [h1]
 have ha' : aᴴ ∈ A := star_mem ha
 exact condExp_inner_eq_zero A X (A.mul_mem ha' hb)
lemma bicommutant_eq (A : StarSubalgebra ℂ (Matrix n n ℂ)) :
  comm (comm A) = A := by
 apply le_antisymm _ (le_commutant_commutant A)
 intro x hx
 let B : n → n → Matrix n n ℂ := fun j k r s =>
  cExp A (Matrix.single s k (1 : ℂ)) r j
 have hcond_eq : ∀ Y : Matrix n n ℂ, ∀ r j : n,
   cExp A Y r j = ∑ k : n, (B j k * Y) r k := by
  intro Y r j
  have hY : Y = ∑ s : n, ∑ k : n, Y s k • Matrix.single s k (1 : ℂ) := by
   ext u v
   simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
   rw [sum_eq_single u]
   ·
    rw [sum_eq_single v]
    · simp
    · intro k _ hkv; simp [hkv]
    · intro h; exact absurd (mem_univ v) h
   ·
    intro s _ hsu
    exact sum_eq_zero fun k _ => by simp [hsu]
   · intro h; exact absurd (mem_univ u) h
  conv_lhs => rw [hY]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_apply]
  refine sum_congr rfl fun s _ => ?_
  dsimp only [B]
  ring
 have hB_mem : ∀ j k : n, B j k ∈ comm A := by
  intro j k a ha
  ext r s
  have hcomm := congrFun (congrFun (condExp_mul_left A ha (Matrix.single s k (1 : ℂ))) r) j
  have h1 : (a * cExp A (Matrix.single s k (1 : ℂ))) r j = (a * B j k) r s := by
   rw [mul_apply, mul_apply]
  have h2 : a * Matrix.single s k (1 : ℂ) = ∑ t : n, a t s • Matrix.single t k (1 : ℂ) := by
   ext u v
   simp only [mul_apply, Matrix.single_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
   rw [sum_eq_single s]
   ·
    rw [sum_eq_single u]
    · simp
    · intro t _ htu; simp [htu]
    · intro h; exact absurd (mem_univ u) h
   · intro t _ hts; simp [hts.symm]
   · intro h; exact absurd (mem_univ s) h
  have h3 : cExp A (a * Matrix.single s k (1 : ℂ)) r j = (B j k * a) r s := by
   rw [h2, map_sum, Matrix.sum_apply, mul_apply]
   refine sum_congr rfl fun t _ => ?_
   rw [map_smul, Matrix.smul_apply, smul_eq_mul]
   dsimp only [B]
   ring
  rw [h1, h3] at hcomm
  exact hcomm
 have hcond_x : cExp A x = x := by
  ext r j
  rw [hcond_eq x r j]
  have hcomm : ∀ k : n, B j k * x = x * B j k := fun k => (hx (B j k) (hB_mem j k)).symm
  simp_rw [hcomm]
  have h1 : ∑ k : n, (x * B j k) r k = (x * cExp A (1 : Matrix n n ℂ)) r j := by
   simp only [mul_apply]
   rw [sum_comm]
   refine sum_congr rfl fun t _ => ?_
   rw [← Finset.mul_sum]
   congr 1
   have h1' := hcond_eq (1 : Matrix n n ℂ) t j
   simp only [mul_one] at h1'
   exact h1'.symm
  rw [h1, condExp_eq_self A.one_mem, mul_one]
 rw [← hcond_x]
 exact condExp_mem A x
end Bicommutant
/- ### 4. Block decomposition (Artin-Wedderburn) for finite-dimensional *-subalgebras -/
section BDec
def bDA {t : ℕ} (r s : Fin t → ℕ)
  (M : (i : Fin t) → Matrix (Fin (r i)) (Fin (r i)) ℂ) :
  Matrix (Σ i : Fin t, Fin (r i) × Fin (s i)) (Σ i : Fin t, Fin (r i) × Fin (s i)) ℂ :=
 fun ⟨i, a, b⟩ ⟨j, c, d⟩ =>
  if h : i = j then (if b = (h ▸ d) then M i a (h ▸ c) else 0) else 0
def bDC {t : ℕ} (r s : Fin t → ℕ)
  (N : (i : Fin t) → Matrix (Fin (s i)) (Fin (s i)) ℂ) :
  Matrix (Σ i : Fin t, Fin (r i) × Fin (s i)) (Σ i : Fin t, Fin (r i) × Fin (s i)) ℂ :=
 fun ⟨i, a, b⟩ ⟨j, c, d⟩ =>
  if h : i = j then (if a = (h ▸ c) then N i b (h ▸ d) else 0) else 0
lemma blockDiagA_mul {t : ℕ} (r s : Fin t → ℕ)
  (M₁ M₂ : (i : Fin t) → Matrix (Fin (r i)) (Fin (r i)) ℂ) :
  bDA r s M₁ * bDA r s M₂ = bDA r s (fun i => M₁ i * M₂ i) := by
 ext ⟨i, a, b⟩ ⟨j, c, d⟩
 simp only [mul_apply, bDA]
 rw [Fintype.sum_sigma]
 rw [sum_eq_single i]
 ·
  simp only [↓reduceDIte]
  by_cases hij : i = j
  ·
   subst hij
   simp only [↓reduceDIte, sum_prod_type]
   by_cases hbd : b = d
   ·
    subst hbd
    simp only [↓reduceIte]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_eq_single b]
    · simp
    · intro l _ hlb; simp [hlb.symm]
    · intro h; exact absurd (mem_univ b) h
   ·
    simp only [if_neg hbd]
    refine sum_eq_zero fun k _ => sum_eq_zero fun l _ => ?_
    by_cases hbl : b = l
    · subst hbl; simp [hbd]
    · simp [hbl]
  · simp only [dif_neg hij, mul_zero, sum_const_zero]
 · intro i' _ hi'; exact sum_eq_zero fun p _ => by simp [Ne.symm hi']
 · intro h; exact absurd (mem_univ i) h
lemma blockDiagC_mul {t : ℕ} (r s : Fin t → ℕ)
  (N₁ N₂ : (i : Fin t) → Matrix (Fin (s i)) (Fin (s i)) ℂ) :
  bDC r s N₁ * bDC r s N₂ = bDC r s (fun i => N₁ i * N₂ i) := by
 ext ⟨i, a, b⟩ ⟨j, c, d⟩
 simp only [mul_apply, bDC]
 rw [Fintype.sum_sigma]
 rw [sum_eq_single i]
 ·
  simp only [↓reduceDIte]
  by_cases hij : i = j
  ·
   subst hij
   simp only [↓reduceDIte, sum_prod_type]
   by_cases hac : a = c
   ·
    subst hac
    simp only [↓reduceIte]
    rw [sum_eq_single a]
    · simp
    · intro k _ hka; exact sum_eq_zero fun l _ => by simp [hka.symm]
    · intro h; exact absurd (mem_univ a) h
   ·
    simp only [if_neg hac]
    refine sum_eq_zero fun k _ => sum_eq_zero fun l _ => ?_
    by_cases hak : a = k
    · subst hak; simp [hac]
    · simp [hak]
  · simp only [dif_neg hij, mul_zero, sum_const_zero]
 · intro i' _ hi'; exact sum_eq_zero fun p _ => by simp [Ne.symm hi']
 · intro h; exact absurd (mem_univ i) h
lemma blockDiagA_comm_blockDiagC {t : ℕ} (r s : Fin t → ℕ)
  (M : (i : Fin t) → Matrix (Fin (r i)) (Fin (r i)) ℂ)
  (N : (i : Fin t) → Matrix (Fin (s i)) (Fin (s i)) ℂ) :
  bDA r s M * bDC r s N = bDC r s N * bDA r s M := by
 ext ⟨i, a, b⟩ ⟨j, c, d⟩
 simp only [mul_apply, bDA, bDC]
 rw [Fintype.sum_sigma, Fintype.sum_sigma]
 rw [sum_eq_single i, sum_eq_single i]
 ·
  simp only [↓reduceDIte]
  by_cases hij : i = j
  ·
   subst hij
   simp only [↓reduceDIte, sum_prod_type]
   have hL : (∑ x : Fin (r i), ∑ y : Fin (s i),
     (if b = y then M i a x else 0) * (if x = c then N i y d else 0)) =
     M i a c * N i b d := by
    rw [sum_eq_single c]
    ·
     rw [sum_eq_single b]
     · simp
     · intro y _ hyb; simp [hyb.symm]
     · intro h; exact absurd (mem_univ b) h
    · intro x _ hxc; exact sum_eq_zero fun y _ => by simp [hxc]
    · intro h; exact absurd (mem_univ c) h
   have hR : (∑ x : Fin (r i), ∑ y : Fin (s i),
     (if a = x then N i b y else 0) * (if y = d then M i x c else 0)) =
     N i b d * M i a c := by
    rw [sum_eq_single a]
    ·
     rw [sum_eq_single d]
     · simp
     · intro y _ hyd; simp [hyd]
     · intro h; exact absurd (mem_univ d) h
    · intro x _ hxa; exact sum_eq_zero fun y _ => by simp [hxa.symm]
    · intro h; exact absurd (mem_univ a) h
   rw [hL, hR, mul_comm]
  · simp [hij]
 · intro i' _ hi'; exact sum_eq_zero fun p _ => by simp [Ne.symm hi']
 · intro h; exact absurd (mem_univ i) h
 · intro i' _ hi'; exact sum_eq_zero fun p _ => by simp [Ne.symm hi']
 · intro h; exact absurd (mem_univ i) h
lemma blockDiagA_conjTranspose {t : ℕ} (r s : Fin t → ℕ)
  (M : (i : Fin t) → Matrix (Fin (r i)) (Fin (r i)) ℂ) :
  (bDA r s M)ᴴ = bDA r s (fun i => (M i)ᴴ) := by
 ext ⟨i, a, b⟩ ⟨j, c, d⟩
 simp only [ctA, bDA]
 by_cases hij : i = j
 ·
  subst hij
  simp only [↓reduceDIte]
  by_cases hbd : b = d
  · subst hbd; simp
  · simp [hbd, Ne.symm hbd]
 · simp [hij, Ne.symm hij]
lemma blockDiagC_conjTranspose {t : ℕ} (r s : Fin t → ℕ)
  (N : (i : Fin t) → Matrix (Fin (s i)) (Fin (s i)) ℂ) :
  (bDC r s N)ᴴ = bDC r s (fun i => (N i)ᴴ) := by
 ext ⟨i, a, b⟩ ⟨j, c, d⟩
 simp only [ctA, bDC]
 by_cases hij : i = j
 ·
  subst hij
  simp only [↓reduceDIte]
  by_cases hac : a = c
  · subst hac; simp
  · simp [hac, Ne.symm hac]
 · simp [hij, Ne.symm hij]
lemma blockDiagA_one {t : ℕ} (r s : Fin t → ℕ) :
  bDA r s (fun _ => 1) = 1 := by
 ext ⟨i, a, b⟩ ⟨j, c, d⟩
 by_cases hij : i = j
 ·
  subst hij
  simp only [bDA, ↓reduceDIte, Matrix.one_apply, Sigma.mk.inj_iff, heq_eq_eq,
   Prod.mk.injEq, true_and]
  by_cases hbd : b = d
  · subst hbd; simp
  · simp [hbd]
 · simp [bDA, hij]
lemma comm_all_blockDiagC_iff {t : ℕ} (r s : Fin t → ℕ) (hs : ∀ i, 0 < s i)
  (X : Matrix (Σ i : Fin t, Fin (r i) × Fin (s i)) (Σ i : Fin t, Fin (r i) × Fin (s i)) ℂ) :
  (∀ N, X * bDC r s N = bDC r s N * X) ↔ ∃ M, X = bDA r s M := by
 constructor
 ·
  intro hcomm
  let M : (i : Fin t) → Matrix (Fin (r i)) (Fin (r i)) ℂ := fun i a c =>
   X ⟨i, a, ⟨0, hs i⟩⟩ ⟨i, c, ⟨0, hs i⟩⟩
  refine ⟨M, ?_⟩
  ext ⟨i, a, b⟩ ⟨j, c, d⟩
  by_cases hij : i = j
  ·
   subst hij
   let N : (k : Fin t) → Matrix (Fin (s k)) (Fin (s k)) ℂ := fun k =>
    if hk : k = i then hk ▸ Matrix.single d ⟨0, hs i⟩ (1 : ℂ) else 0
   have h1 := congrFun (congrFun (hcomm N) ⟨i, a, b⟩) ⟨i, c, ⟨0, hs i⟩⟩
   simp only [mul_apply, bDC] at h1
   rw [Fintype.sum_sigma, Fintype.sum_sigma] at h1
   rw [sum_eq_single i, sum_eq_single i] at h1
   ·
    simp only [↓reduceDIte, sum_prod_type] at h1
    rw [sum_eq_single c, sum_eq_single a] at h1
    ·
     simp only [↓reduceIte, N, ↓reduceDIte] at h1
     rw [sum_eq_single d, sum_eq_single ⟨0, hs i⟩] at h1
     ·
      simp only [Matrix.single_apply, and_true, ↓reduceIte, mul_one] at h1
      by_cases hbd : b = d
      ·
       subst hbd
       simp only [↓reduceIte, one_mul] at h1
       simp [bDA, M, h1]
      ·
       simp only [if_neg (Ne.symm hbd), zero_mul] at h1
       simp only [bDA, ↓reduceDIte, if_neg hbd]
       exact h1
     · intro l _ hl; simp [hl.symm]
     · intro h; exact absurd (mem_univ _) h
     · intro l _ hl; simp [hl.symm]
     · intro h; exact absurd (mem_univ d) h
    · intro k _ hka; exact sum_eq_zero fun l _ => by simp [hka.symm]
    · intro h; exact absurd (mem_univ a) h
    · intro k _ hkc; exact sum_eq_zero fun l _ => by simp [hkc]
    · intro h; exact absurd (mem_univ c) h
   · intro k _ hki; exact sum_eq_zero fun p _ => by simp [Ne.symm hki]
   · intro h; exact absurd (mem_univ i) h
   · intro k _ hki; exact sum_eq_zero fun p _ => by simp [hki]
   · intro h; exact absurd (mem_univ i) h
  ·
   let N : (k : Fin t) → Matrix (Fin (s k)) (Fin (s k)) ℂ := fun k =>
    if k = j then 1 else 0
   have h1 := congrFun (congrFun (hcomm N) ⟨i, a, b⟩) ⟨j, c, d⟩
   simp only [mul_apply, bDC] at h1
   rw [Fintype.sum_sigma, Fintype.sum_sigma] at h1
   rw [sum_eq_single j, sum_eq_single i] at h1
   ·
    simp only [↓reduceDIte, N, ↓reduceIte, if_neg hij, Matrix.zero_apply, ite_self, zero_mul,
     sum_const_zero] at h1
    rw [sum_prod_type, sum_eq_single c, sum_eq_single d] at h1
    ·
     simp only [↓reduceIte, Matrix.one_apply_eq, mul_one] at h1
     simp [bDA, hij, h1]
    · intro l _ hld; simp [Matrix.one_apply_ne hld]
    · intro h; exact absurd (mem_univ d) h
    · intro k _ hkc; exact sum_eq_zero fun l _ => by simp [hkc]
    · intro h; exact absurd (mem_univ c) h
   · intro k _ hki; exact sum_eq_zero fun p _ => by simp [Ne.symm hki]
   · intro h; exact absurd (mem_univ i) h
   · intro k _ hkj; exact sum_eq_zero fun p _ => by simp [hkj]
   · intro h; exact absurd (mem_univ j) h
 ·
  rintro ⟨M, rfl⟩ N
  exact blockDiagA_comm_blockDiagC r s M N
lemma comm_all_blockDiagA_iff {t : ℕ} (r s : Fin t → ℕ) (hr : ∀ i, 0 < r i)
  (X : Matrix (Σ i : Fin t, Fin (r i) × Fin (s i)) (Σ i : Fin t, Fin (r i) × Fin (s i)) ℂ) :
  (∀ M, X * bDA r s M = bDA r s M * X) ↔ ∃ N, X = bDC r s N := by
 let e : (Σ i : Fin t, Fin (s i) × Fin (r i)) ≃ (Σ i : Fin t, Fin (r i) × Fin (s i)) :=
  {
   toFun := fun ⟨i, b, a⟩ => ⟨i, a, b⟩
   invFun := fun ⟨i, a, b⟩ => ⟨i, b, a⟩
   left_inv := fun ⟨_, _, _⟩ => rfl
   right_inv := fun ⟨_, _, _⟩ => rfl }
 have h1 : ∀ M, Matrix.submatrix (bDA r s M) e e = bDC s r M := by
  intro M; ext ⟨i, b, a⟩ ⟨j, d, c⟩
  by_cases hij : i = j
  · subst hij; simp [bDA, bDC, e]
  · simp [bDA, bDC, e, hij]
 have h2 : ∀ N, Matrix.submatrix (bDC r s N) e e = bDA s r N := by
  intro N; ext ⟨i, b, a⟩ ⟨j, d, c⟩
  by_cases hij : i = j
  · subst hij; simp [bDA, bDC, e]
  · simp [bDA, bDC, e, hij]
 have hiff := comm_all_blockDiagC_iff s r hr (Matrix.submatrix X e e)
 constructor
 ·
  intro hcomm
  have hcomm' : ∀ M, Matrix.submatrix X e e * bDC s r M =
    bDC s r M * Matrix.submatrix X e e := by
   intro M
   rw [← h1 M, Matrix.submatrix_mul_equiv X (bDA r s M) e e e,
    Matrix.submatrix_mul_equiv (bDA r s M) X e e e, hcomm M]
  obtain ⟨N, hN⟩ := hiff.mp hcomm'
  refine ⟨N, ?_⟩
  ext p q
  have hp := congrFun (congrFun hN (e.symm p)) (e.symm q)
  rw [← h2 N] at hp
  simpa [Matrix.submatrix_apply] using hp
 ·
  rintro ⟨N, rfl⟩ M
  exact (blockDiagA_comm_blockDiagC r s M N).symm
structure BDec {n : Type*} [Fintype n] [DecidableEq n]
  (A : StarSubalgebra ℂ (Matrix n n ℂ)) where
 t : ℕ
 r : Fin t → ℕ
 s : Fin t → ℕ
 hr : ∀ i, 0 < r i
 hs : ∀ i, 0 < s i
 U : Matrix n (Σ i : Fin t, Fin (r i) × Fin (s i)) ℂ
 U_star_mul : Uᴴ * U = 1
 U_mul_star : U * Uᴴ = 1
 mem_iff : ∀ X : Matrix n n ℂ, X ∈ A ↔
  ∃ M : (i : Fin t) → Matrix (Fin (r i)) (Fin (r i)) ℂ,
   Uᴴ * X * U = bDA r s M
lemma bDec_comm_iff {n : Type*} [Fintype n] [DecidableEq n]
  {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A) (X : Matrix n n ℂ) :
  X ∈ comm A ↔
   ∃ N : (i : Fin bd.t) → Matrix (Fin (bd.s i)) (Fin (bd.s i)) ℂ,
    bd.Uᴴ * X * bd.U = bDC bd.r bd.s N := by
 rw [← comm_all_blockDiagA_iff bd.r bd.s bd.hr (bd.Uᴴ * X * bd.U)]
 constructor
 ·
  intro hX M
  let a := bd.U * bDA bd.r bd.s M * bd.Uᴴ
  have ha : a ∈ A := by
   rw [bd.mem_iff]
   refine ⟨M, ?_⟩
   simp only [a]
   calc
    bd.Uᴴ * (bd.U * bDA bd.r bd.s M * bd.Uᴴ) * bd.U
     = (bd.Uᴴ * bd.U) * bDA bd.r bd.s M * (bd.Uᴴ * bd.U) := by simp [mma]
    _ = bDA bd.r bd.s M := by rw [bd.U_star_mul, m1m, mm1]
  have hcomm := hX a ha
  have hconj := congrArg (fun Z => bd.Uᴴ * Z * bd.U) hcomm
  have hL : bd.Uᴴ * (X * a) * bd.U = (bd.Uᴴ * X * bd.U) * bDA bd.r bd.s M := by
   simp only [a]
   calc
    bd.Uᴴ * (X * (bd.U * bDA bd.r bd.s M * bd.Uᴴ)) * bd.U
     = (bd.Uᴴ * X * bd.U) * bDA bd.r bd.s M * (bd.Uᴴ * bd.U) := by simp [mma]
    _ = (bd.Uᴴ * X * bd.U) * bDA bd.r bd.s M := by rw [bd.U_star_mul, mm1]
  have hR : bd.Uᴴ * (a * X) * bd.U = bDA bd.r bd.s M * (bd.Uᴴ * X * bd.U) := by
   simp only [a]
   calc
    bd.Uᴴ * ((bd.U * bDA bd.r bd.s M * bd.Uᴴ) * X) * bd.U
     = (bd.Uᴴ * bd.U) * (bDA bd.r bd.s M * (bd.Uᴴ * X * bd.U)) := by simp [mma]
    _ = bDA bd.r bd.s M * (bd.Uᴴ * X * bd.U) := by rw [bd.U_star_mul, m1m]
  rw [hL, hR] at hconj
  exact hconj
 ·
  intro hcomm a ha
  obtain ⟨M, hM⟩ := (bd.mem_iff a).mp ha
  have ha_eq : a = bd.U * bDA bd.r bd.s M * bd.Uᴴ := by
   rw [← hM]
   calc
    a = 1 * a * 1 := by simp
    _ = (bd.U * bd.Uᴴ) * a * (bd.U * bd.Uᴴ) := by rw [bd.U_mul_star]
    _ = bd.U * (bd.Uᴴ * a * bd.U) * bd.Uᴴ := by simp [mma]
  have hX_eq : X = bd.U * (bd.Uᴴ * X * bd.U) * bd.Uᴴ := by
   calc
    X = 1 * X * 1 := by simp
    _ = (bd.U * bd.Uᴴ) * X * (bd.U * bd.Uᴴ) := by rw [bd.U_mul_star]
    _ = bd.U * (bd.Uᴴ * X * bd.U) * bd.Uᴴ := by simp [mma]
  rw [hX_eq, ha_eq]
  calc
   (bd.U * (bd.Uᴴ * X * bd.U) * bd.Uᴴ) * (bd.U * bDA bd.r bd.s M * bd.Uᴴ)
    = bd.U * ((bd.Uᴴ * X * bd.U) * ((bd.Uᴴ * bd.U) * bDA bd.r bd.s M)) * bd.Uᴴ := by
      simp [mma]
   _ = bd.U * ((bd.Uᴴ * X * bd.U) * bDA bd.r bd.s M) * bd.Uᴴ := by
      rw [bd.U_star_mul, m1m]
   _ = bd.U * (bDA bd.r bd.s M * (bd.Uᴴ * X * bd.U)) * bd.Uᴴ := by rw [hcomm M]
   _ = bd.U * (bDA bd.r bd.s M * ((bd.Uᴴ * bd.U) * (bd.Uᴴ * X * bd.U))) * bd.Uᴴ := by
      rw [bd.U_star_mul, m1m]
   _ = (bd.U * bDA bd.r bd.s M * bd.Uᴴ) * (bd.U * (bd.Uᴴ * X * bd.U) * bd.Uᴴ) := by
      simp [mma]
/- Construction of BDec via orthogonal irreducible decomposition + Schur's lemma -/
section ExistsBlockDecomp
variable {n : Type*} [Fintype n] [DecidableEq n]
def IsInv (A : StarSubalgebra ℂ (Matrix n n ℂ))
  (V : Submodule ℂ (EuclideanSpace ℂ n)) : Prop :=
 ∀ a ∈ A, ∀ v ∈ V, toEuclideanCLM (n := n) (𝕜 := ℂ) a v ∈ V
def IsIrred (A : StarSubalgebra ℂ (Matrix n n ℂ))
  (V : Submodule ℂ (EuclideanSpace ℂ n)) : Prop :=
 V ≠ ⊥ ∧ IsInv A V ∧ ∀ W ≤ V, IsInv A W → W = ⊥ ∨ W = V
lemma toCLM_adjoint (A : Matrix n n ℂ) :
  ContinuousLinearMap.adjoint (CLM A) = CLM Aᴴ := by
 change star (toEuclideanCLM (n := n) (𝕜 := ℂ) A) =
  toEuclideanCLM (n := n) (𝕜 := ℂ) (star A)
 exact (map_star (toEuclideanCLM (n := n) (𝕜 := ℂ)) A).symm
lemma starProjection_eq_zero_of_mem_orthogonal {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E] (K : Submodule ℂ E) [K.HasOrthogonalProjection]
  {x : E} (hx : x ∈ Kᗮ) : K.starProjection x = 0 := by
 have h1 : ⟪K.starProjection x, K.starProjection x⟫_ℂ = 0 := by
  have hmem : K.starProjection x ∈ K := (K.orthogonalProjectionOnto x).2
  have h0 := K.starProjection_inner_eq_zero x (K.starProjection x) hmem
  have hx0 : ⟪K.starProjection x, x⟫_ℂ = 0 := (Submodule.mem_orthogonal K x).mp hx _ hmem
  have hx0' : ⟪x, K.starProjection x⟫_ℂ = 0 := by rw [← inner_conj_symm, hx0, map_zero]
  rw [inner_sub_left, hx0', zero_sub, neg_eq_zero] at h0
  exact h0
 exact inner_self_eq_zero.mp h1
omit [DecidableEq n] in
lemma submodule_isometry_inner {V W : Submodule ℂ (EuclideanSpace ℂ n)}
  (Φ : V ≃ₗᵢ[ℂ] W) (x y : V) :
  ⟪(Φ x : EuclideanSpace ℂ n), (Φ y : EuclideanSpace ℂ n)⟫_ℂ =
   ⟪(x : EuclideanSpace ℂ n), (y : EuclideanSpace ℂ n)⟫_ℂ := by
 have hpol : ∀ u v : EuclideanSpace ℂ n,
   (4 : ℂ) * ⟪u, v⟫_ℂ =
    (⟪u + v, u + v⟫_ℂ - ⟪u - v, u - v⟫_ℂ) -
     Complex.I * (⟪u + Complex.I • v, u + Complex.I • v⟫_ℂ -
      ⟪u - Complex.I • v, u - Complex.I • v⟫_ℂ) := by
  intro u v
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
   inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]
  ring
 have hsq : ∀ z : V, ⟪(Φ z : EuclideanSpace ℂ n), (Φ z : EuclideanSpace ℂ n)⟫_ℂ =
   ⟪(z : EuclideanSpace ℂ n), (z : EuclideanSpace ℂ n)⟫_ℂ := by
  intro z
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  have hn : ‖(Φ z : EuclideanSpace ℂ n)‖ = ‖(z : EuclideanSpace ℂ n)‖ := Φ.norm_map z
  rw [hn]
 have h1 : (4 : ℂ) * ⟪(Φ x : EuclideanSpace ℂ n), (Φ y : EuclideanSpace ℂ n)⟫_ℂ =
   (4 : ℂ) * ⟪(x : EuclideanSpace ℂ n), (y : EuclideanSpace ℂ n)⟫_ℂ := by
  rw [hpol, hpol]
  have ha := hsq (x + y)
  have hb := hsq (x - y)
  have hc := hsq (x + Complex.I • y)
  have hd := hsq (x - Complex.I • y)
  simp only [map_add, map_sub, map_smul, Submodule.coe_add, Submodule.coe_sub,
   SetLike.val_smul] at ha hb hc hd
  rw [ha, hb, hc, hd]
 exact mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0) h1
lemma isInv_orthogonal {A : StarSubalgebra ℂ (Matrix n n ℂ)}
  {V : Submodule ℂ (EuclideanSpace ℂ n)} (hV : IsInv A V) : IsInv A Vᗮ := by
 intro a ha v hv
 rw [Submodule.mem_orthogonal]
 intro w hw
 have hstar : toEuclideanCLM (n := n) (𝕜 := ℂ) a =
   ContinuousLinearMap.adjoint (toEuclideanCLM (n := n) (𝕜 := ℂ) aᴴ) := by
  change CLM a = ContinuousLinearMap.adjoint (CLM aᴴ)
  rw [toCLM_adjoint, ctct]
 rw [hstar, ContinuousLinearMap.adjoint_inner_right]
 have ha' : aᴴ ∈ A := star_mem ha
 exact (Submodule.mem_orthogonal V v).mp hv _ (hV aᴴ ha' w hw)
lemma exists_irred_decomp (A : StarSubalgebra ℂ (Matrix n n ℂ))
  (W : Submodule ℂ (EuclideanSpace ℂ n)) (hW : IsInv A W) :
  ∃ (L : ℕ) (V : Fin L → Submodule ℂ (EuclideanSpace ℂ n)),
   (∀ k, IsIrred A (V k)) ∧
   (∀ k l, k ≠ l → ∀ x ∈ V k, ∀ y ∈ V l, ⟪x, y⟫_ℂ = 0) ∧
   ⨆ k, V k = W := by
 suffices h : ∀ d : ℕ, ∀ W : Submodule ℂ (EuclideanSpace ℂ n),
   IsInv A W → Module.finrank ℂ W = d →
   ∃ (L : ℕ) (V : Fin L → Submodule ℂ (EuclideanSpace ℂ n)),
    (∀ k, IsIrred A (V k)) ∧
    (∀ k l, k ≠ l → ∀ x ∈ V k, ∀ y ∈ V l, ⟪x, y⟫_ℂ = 0) ∧
    ⨆ k, V k = W from h _ W hW rfl
 intro d
 induction d using Nat.strong_induction_on with
 | _ d ih =>
  intro W hW hd
  by_cases hbot : W = ⊥
  ·
   refine ⟨0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, ?_⟩
   simp [hbot]
  ·
   by_cases hirr : IsIrred A W
   ·
    refine ⟨1, fun _ => W, fun _ => hirr, fun k l hkl => absurd (Subsingleton.elim k l) hkl, ?_⟩
    simp
   ·
    have hprop : ∃ U ≤ W, IsInv A U ∧ U ≠ ⊥ ∧ U ≠ W := by
     unfold IsIrred at hirr
     push Not at hirr
     exact hirr hbot hW
    obtain ⟨U, hUW, hUinv, hUbot, hUneW⟩ := hprop
    let U' : Submodule ℂ (EuclideanSpace ℂ n) := Uᗮ ⊓ W
    have hU'inv : IsInv A U' := fun a ha v hv =>
     ⟨isInv_orthogonal hUinv a ha v hv.1, hW a ha v hv.2⟩
    have hsup : U ⊔ U' = W :=
     Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hUW
    have hadd : Module.finrank ℂ U + Module.finrank ℂ U' = Module.finrank ℂ W :=
     Submodule.finrank_add_inf_finrank_orthogonal hUW
    have hUpos : 0 < Module.finrank ℂ U :=
     Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hUbot)
    have hUlt : Module.finrank ℂ U < d := by
     rw [← hd]
     exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hUW hUneW)
    have hU'lt : Module.finrank ℂ U' < d := by omega
    obtain ⟨L₁, V₁, h1i, h1o, h1s⟩ := ih _ hUlt U hUinv rfl
    obtain ⟨L₂, V₂, h2i, h2o, h2s⟩ := ih _ hU'lt U' hU'inv rfl
    let V : Fin (L₁ + L₂) → Submodule ℂ (EuclideanSpace ℂ n) :=
     Fin.addCases V₁ V₂
    refine ⟨L₁ + L₂, V, ?_, ?_, ?_⟩
    ·
     intro k
     refine Fin.addCases (fun i => ?_) (fun j => ?_) k
     · simpa [V] using h1i i
     · simpa [V] using h2i j
    ·
     intro k l
     refine Fin.addCases (fun k₁ => ?_) (fun k₂ => ?_) k
     ·
      refine Fin.addCases (fun l₁ => ?_) (fun l₂ => ?_) l
      ·
       intro hkl' x hx' y hy'
       simp only [V, Fin.addCases_left] at hx' hy'
       have hne : k₁ ≠ l₁ := fun h => hkl' (congrArg (Fin.castAdd L₂) h)
       exact h1o k₁ l₁ hne x hx' y hy'
      ·
       intro _ x hx' y hy'
       simp only [V, Fin.addCases_left, Fin.addCases_right] at hx' hy'
       have hxU : x ∈ U := h1s ▸ Submodule.mem_iSup_of_mem k₁ hx'
       have hyU' : y ∈ U' := h2s ▸ Submodule.mem_iSup_of_mem l₂ hy'
       exact (Submodule.mem_orthogonal U y).mp hyU'.1 x hxU
     ·
      refine Fin.addCases (fun l₁ => ?_) (fun l₂ => ?_) l
      ·
       intro _ x hx' y hy'
       simp only [V, Fin.addCases_left, Fin.addCases_right] at hx' hy'
       have hxU' : x ∈ U' := h2s ▸ Submodule.mem_iSup_of_mem k₂ hx'
       have hyU : y ∈ U := h1s ▸ Submodule.mem_iSup_of_mem l₁ hy'
       have h0 := (Submodule.mem_orthogonal U x).mp hxU'.1 y hyU
       rw [← inner_conj_symm, h0, map_zero]
      ·
       intro hkl' x hx' y hy'
       simp only [V, Fin.addCases_right] at hx' hy'
       have hne : k₂ ≠ l₂ := fun h => hkl' (congrArg (Fin.natAdd L₁) h)
       exact h2o k₂ l₂ hne x hx' y hy'
    ·
     apply le_antisymm
     ·
      refine iSup_le fun k => ?_
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      ·
       simp only [V, Fin.addCases_left]
       exact (le_iSup V₁ i).trans (h1s.le.trans hUW)
      ·
       simp only [V, Fin.addCases_right]
       exact (le_iSup V₂ j).trans (h2s.le.trans inf_le_right)
     ·
      rw [← hsup, ← h1s, ← h2s]
      refine sup_le (iSup_le fun i => ?_) (iSup_le fun j => ?_)
      ·
       have : V₁ i = V (Fin.castAdd L₂ i) := by simp [V]
       rw [this]; exact le_iSup V _
      ·
       have : V₂ j = V (Fin.natAdd L₁ j) := by simp [V]
       rw [this]; exact le_iSup V _
lemma schur_end_eq_smul {A : StarSubalgebra ℂ (Matrix n n ℂ)}
  {V : Submodule ℂ (EuclideanSpace ℂ n)} (hV : IsIrred A V)
  (T : V →ₗ[ℂ] V)
  (hT : ∀ a (ha : a ∈ A) (v : V),
   (T ⟨CLM a v.1, hV.2.1 a ha v.1 v.2⟩ : EuclideanSpace ℂ n) = CLM a (T v).1) :
  ∃ c : ℂ, T = c • LinearMap.id := by
 have hnt : Nontrivial V := by
  rw [Submodule.nontrivial_iff_ne_bot]; exact hV.1
 obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
 let K : Submodule ℂ (EuclideanSpace ℂ n) :=
  (LinearMap.ker (T - c • LinearMap.id)).map V.subtype
 have hKV : K ≤ V := by
  rintro _ ⟨v, _, rfl⟩; exact v.2
 have hKinv : IsInv A K := by
  rintro a ha _ ⟨v, hv, rfl⟩
  refine ⟨⟨CLM a v.1, hV.2.1 a ha v.1 v.2⟩, ?_, rfl⟩
  change v ∈ LinearMap.ker (T - c • LinearMap.id) at hv
  change (⟨CLM a v.1, hV.2.1 a ha v.1 v.2⟩ : V) ∈ LinearMap.ker (T - c • LinearMap.id)
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
   sub_eq_zero] at hv ⊢
  apply Subtype.ext
  rw [hT a ha v, hv]
  simp [map_smul]
 have hKne : K ≠ ⊥ := by
  intro hbot
  apply hc
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hv' : v ∈ LinearMap.ker (T - c • LinearMap.id) := by
   rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
   exact Module.End.mem_eigenspace_iff.mp hv
  have hvK : (v : EuclideanSpace ℂ n) ∈ K := ⟨v, hv', rfl⟩
  rw [hbot, Submodule.mem_bot] at hvK
  exact Subtype.ext hvK
 have hKeq : K = V := (hV.2.2 K hKV hKinv).resolve_left hKne
 refine ⟨c, ?_⟩
 apply LinearMap.ext
 intro v
 have hvK : (v : EuclideanSpace ℂ n) ∈ K := by rw [hKeq]; exact v.2
 rcases hvK with ⟨w, hw, hwv⟩
 have hweq : w = v := Subtype.ext hwv
 subst hweq
 have hw' : w ∈ LinearMap.ker (T - c • LinearMap.id) := hw
 rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
  sub_eq_zero] at hw'
 exact hw'
def IsoInv (A : StarSubalgebra ℂ (Matrix n n ℂ))
  (V W : Submodule ℂ (EuclideanSpace ℂ n)) : Prop :=
 ∃ Φ : V ≃ₗᵢ[ℂ] W, ∀ a ∈ A, ∀ v : V,
  (Φ.toLinearEquiv v : EuclideanSpace ℂ n) = (Φ v : EuclideanSpace ℂ n) ∧
  ∀ hv : CLM a v.1 ∈ V,
   (Φ ⟨CLM a v.1, hv⟩ : EuclideanSpace ℂ n) = CLM a (Φ v).1
lemma isoInv_of_nonzero_intertwiner {A : StarSubalgebra ℂ (Matrix n n ℂ)}
  {V W : Submodule ℂ (EuclideanSpace ℂ n)} (hV : IsIrred A V) (hW : IsIrred A W)
  (T : V →ₗ[ℂ] W) (hTne : T ≠ 0)
  (hT : ∀ a (ha : a ∈ A) (v : V),
   (T ⟨CLM a v.1, hV.2.1 a ha v.1 v.2⟩ : EuclideanSpace ℂ n) = CLM a (T v).1) :
  IsoInv A V W := by
 let Ts : W →ₗ[ℂ] V := (LinearMap.adjoint (𝕜 := ℂ) (E := ↥V) (F := ↥W) T)
 have hTs : ∀ a (ha : a ∈ A) (w : W),
   (Ts ⟨CLM a w.1, hW.2.1 a ha w.1 w.2⟩ : EuclideanSpace ℂ n) = CLM a (Ts w).1 := by
  intro a ha w
  have hsub : Ts ⟨CLM a w.1, hW.2.1 a ha w.1 w.2⟩ =
    ⟨CLM a (Ts w).1, hV.2.1 a ha (Ts w).1 (Ts w).2⟩ := by
   apply ext_inner_left ℂ
   intro v
   rw [LinearMap.adjoint_inner_right]
   change ⟪(T v).1, CLM a w.1⟫_ℂ = ⟪v.1, CLM a (Ts w).1⟫_ℂ
   have hstar : CLM a = ContinuousLinearMap.adjoint (CLM aᴴ) := by
    rw [toCLM_adjoint, ctct]
   rw [hstar, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
   have ha' : aᴴ ∈ A := star_mem ha
   have h1 := hT aᴴ ha' v
   rw [← h1]
   let u : V := ⟨CLM aᴴ v.1, hV.2.1 aᴴ ha' v.1 v.2⟩
   change ⟪T u, w⟫_ℂ = ⟪u, Ts w⟫_ℂ
   rw [LinearMap.adjoint_inner_right]
  exact congrArg Subtype.val hsub
 obtain ⟨c, hc⟩ := schur_end_eq_smul hV (Ts.comp T) fun a ha v => by
  have h1 : T ⟨CLM a v.1, hV.2.1 a ha v.1 v.2⟩ =
    ⟨CLM a (T v).1, hW.2.1 a ha (T v).1 (T v).2⟩ :=
   Subtype.ext (hT a ha v)
  simp only [LinearMap.comp_apply, h1]
  exact hTs a ha (T v)
 have hv0 : ∃ v₀ : V, T v₀ ≠ 0 := by
  by_contra h
  push Not at h
  exact hTne (LinearMap.ext h)
 obtain ⟨v₀, hv₀⟩ := hv0
 have hv₀_ne : v₀ ≠ 0 := fun h => hv₀ (by simp [h])
 have hinner : ⟪(T v₀ : EuclideanSpace ℂ n), (T v₀ : EuclideanSpace ℂ n)⟫_ℂ =
   c * ⟪(v₀ : EuclideanSpace ℂ n), (v₀ : EuclideanSpace ℂ n)⟫_ℂ := by
  have h1 : ⟪v₀, (Ts.comp T) v₀⟫_ℂ = ⟪T v₀, T v₀⟫_ℂ := by
   change ⟪v₀, Ts (T v₀)⟫_ℂ = ⟪T v₀, T v₀⟫_ℂ
   rw [LinearMap.adjoint_inner_right]
  have h2 : ⟪v₀, (Ts.comp T) v₀⟫_ℂ =
    c * ⟪(v₀ : EuclideanSpace ℂ n), (v₀ : EuclideanSpace ℂ n)⟫_ℂ := by
   rw [hc, LinearMap.smul_apply, LinearMap.id_apply]
   change ⟪(v₀ : EuclideanSpace ℂ n), c • (v₀ : EuclideanSpace ℂ n)⟫_ℂ = _
   rw [inner_smul_right]
  exact h1.symm.trans h2
 have hnorm_pos : (0 : ℝ) < ‖v₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv₀_ne)
 have hTnorm_pos : (0 : ℝ) < ‖T v₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv₀)
 have hc_eq : c = ((‖T v₀‖ ^ 2 / ‖v₀‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
  have hcast1 : ((‖(T v₀ : EuclideanSpace ℂ n)‖ : ℝ) : ℂ) ^ 2 = ((‖T v₀‖ ^ 2 : ℝ) : ℂ) := by
   push_cast; rfl
  have hcast2 : ((‖(v₀ : EuclideanSpace ℂ n)‖ : ℝ) : ℂ) ^ 2 = ((‖v₀‖ ^ 2 : ℝ) : ℂ) := by
   push_cast; rfl
  simp only [Complex.coe_algebraMap] at hinner
  rw [hcast1, hcast2] at hinner
  have hne : ((‖v₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hnorm_pos)
  rw [Complex.ofReal_div]
  apply mul_right_cancel₀ hne
  rw [div_mul_cancel₀ _ hne]
  exact hinner.symm
 let lam : ℝ := ‖T v₀‖ ^ 2 / ‖v₀‖ ^ 2
 have hlam : 0 < lam := div_pos hTnorm_pos hnorm_pos
 let f : V →ₗ[ℂ] W := ((sqrt lam)⁻¹ : ℂ) • T
 have hf_iso : ∀ v : V, ‖f v‖ = ‖v‖ := by
  intro v
  have hsq : ‖f v‖ ^ 2 = ‖v‖ ^ 2 := by
   have h1 : ((‖f v‖ ^ 2 : ℝ) : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    have hfv : ((‖f v‖ ^ 2 : ℝ) : ℂ) =
      ⟪(f v : EuclideanSpace ℂ n), (f v : EuclideanSpace ℂ n)⟫_ℂ := by
     rw [inner_self_eq_norm_sq_to_K]; simp
    have hv' : ((‖v‖ ^ 2 : ℝ) : ℂ) =
      ⟪(v : EuclideanSpace ℂ n), (v : EuclideanSpace ℂ n)⟫_ℂ := by
     rw [inner_self_eq_norm_sq_to_K]; simp
    rw [hfv, hv']
    change ⟪((sqrt lam)⁻¹ : ℂ) • (T v : EuclideanSpace ℂ n),
      ((sqrt lam)⁻¹ : ℂ) • (T v : EuclideanSpace ℂ n)⟫_ℂ =
     ⟪(v : EuclideanSpace ℂ n), (v : EuclideanSpace ℂ n)⟫_ℂ
    rw [inner_smul_left, inner_smul_right]
    have hadj : ⟪(T v : EuclideanSpace ℂ n), (T v : EuclideanSpace ℂ n)⟫_ℂ =
      (lam : ℂ) * ⟪(v : EuclideanSpace ℂ n), (v : EuclideanSpace ℂ n)⟫_ℂ := by
     have h0 : ⟪v, (Ts.comp T) v⟫_ℂ = ⟪T v, T v⟫_ℂ := by
      change ⟪v, Ts (T v)⟫_ℂ = ⟪T v, T v⟫_ℂ
      rw [LinearMap.adjoint_inner_right]
     have h2 : ⟪v, (Ts.comp T) v⟫_ℂ =
       (lam : ℂ) * ⟪(v : EuclideanSpace ℂ n), (v : EuclideanSpace ℂ n)⟫_ℂ := by
      rw [hc, LinearMap.smul_apply, LinearMap.id_apply, hc_eq]
      change ⟪(v : EuclideanSpace ℂ n), (lam : ℂ) • (v : EuclideanSpace ℂ n)⟫_ℂ = _
      rw [inner_smul_right]
     exact h0.symm.trans h2
    rw [hadj]
    have hconj : (starRingEnd ℂ) ((sqrt lam)⁻¹ : ℂ) = ((sqrt lam)⁻¹ : ℂ) := by
     rw [← Complex.ofReal_inv]; exact conj_ofReal _
    rw [hconj, ← mul_assoc, ← mul_assoc]
    have hmul : ((sqrt lam)⁻¹ : ℂ) * ((sqrt lam)⁻¹ : ℂ) * (lam : ℂ) = 1 := by
     rw [← Complex.ofReal_inv, ← ofReal_mul, ← ofReal_mul, ← mul_inv,
      mul_self_sqrt hlam.le, inv_mul_cancel₀ (ne_of_gt hlam), Complex.ofReal_one]
    rw [hmul, one_mul]
   exact_mod_cast h1
  nlinarith [norm_nonneg (f v), norm_nonneg v]
 let fi : V →ₗᵢ[ℂ] W := ⟨f, hf_iso⟩
 have hsurj : Function.Surjective fi := by
  let R : Submodule ℂ (EuclideanSpace ℂ n) := (LinearMap.range f).map W.subtype
  have hRW : R ≤ W := by rintro _ ⟨w, _, rfl⟩; exact w.2
  have hRinv : IsInv A R := by
   rintro a ha _ ⟨_, ⟨v, rfl⟩, rfl⟩
   refine ⟨⟨CLM a (f v).1, hW.2.1 a ha (f v).1 (f v).2⟩, ?_, rfl⟩
   refine ⟨⟨CLM a v.1, hV.2.1 a ha v.1 v.2⟩, ?_⟩
   apply Subtype.ext
   simp only [f, LinearMap.smul_apply, SetLike.val_smul, map_smul]
   rw [hT a ha v]
  have hRne : R ≠ ⊥ := by
   intro hbot
   have hmem : (f v₀ : EuclideanSpace ℂ n) ∈ R := ⟨f v₀, ⟨v₀, rfl⟩, rfl⟩
   rw [hbot, Submodule.mem_bot] at hmem
   have h0 : f v₀ = 0 := Subtype.ext hmem
   have hnorm := hf_iso v₀
   rw [h0, norm_zero] at hnorm
   exact hv₀_ne (norm_eq_zero.mp hnorm.symm)
  have hReq : R = W := (hW.2.2 R hRW hRinv).resolve_left hRne
  intro w
  have hwR : (w : EuclideanSpace ℂ n) ∈ R := by rw [hReq]; exact w.2
  rcases hwR with ⟨w', ⟨v, rfl⟩, hw'⟩
  exact ⟨v, Subtype.ext hw'⟩
 let Φ : V ≃ₗᵢ[ℂ] W := LinearIsometryEquiv.ofSurjective fi hsurj
 refine ⟨Φ, fun a ha v => ⟨rfl, fun hv => ?_⟩⟩
 change (f ⟨CLM a v.1, hv⟩ : EuclideanSpace ℂ n) = CLM a (f v).1
 simp only [f, LinearMap.smul_apply, SetLike.val_smul, map_smul]
 rw [hT a ha v]
lemma exists_blockDecomp (A : StarSubalgebra ℂ (Matrix n n ℂ)) :
  Nonempty (BDec A) := by
 classical
 obtain ⟨L, V, hVirr, hVorth, hVsup⟩ :=
  exists_irred_decomp A ⊤ (fun _ _ _ _ => trivial)
 have hiso_refl : ∀ k, IsoInv A (V k) (V k) := fun k =>
  ⟨LinearIsometryEquiv.refl ℂ (V k), fun _ _ _ => ⟨rfl, fun _ => rfl⟩⟩
 have hiso_symm : ∀ {k l}, IsoInv A (V k) (V l) → IsoInv A (V l) (V k) := by
  rintro k l ⟨Φ, hΦ⟩
  refine ⟨Φ.symm, fun a ha w => ⟨rfl, fun hw => ?_⟩⟩
  have h1 := (hΦ a ha (Φ.symm w)).2 ((hVirr k).2.1 a ha (Φ.symm w).1 (Φ.symm w).2)
  have h2 : Φ ⟨CLM a (Φ.symm w).1, (hVirr k).2.1 a ha (Φ.symm w).1 (Φ.symm w).2⟩ =
    ⟨CLM a w.1, hw⟩ := by
   apply Subtype.ext
   simpa using h1
  have h3 := congrArg (fun z => (Φ.symm z : EuclideanSpace ℂ n)) h2
  simpa using h3.symm
 have hiso_trans : ∀ {k l m}, IsoInv A (V k) (V l) → IsoInv A (V l) (V m) → IsoInv A (V k) (V m) := by
  rintro k l m ⟨Φ₁, h1⟩ ⟨Φ₂, h2⟩
  refine ⟨Φ₁.trans Φ₂, fun a ha v => ⟨rfl, fun hv => ?_⟩⟩
  have hv1 := (h1 a ha v).2 hv
  have hv' : Φ₁ ⟨CLM a v.1, hv⟩ =
    ⟨CLM a (Φ₁ v).1, (hVirr l).2.1 a ha (Φ₁ v).1 (Φ₁ v).2⟩ :=
   Subtype.ext hv1
  change (Φ₂ (Φ₁ ⟨CLM a v.1, hv⟩) : EuclideanSpace ℂ n) = _
  rw [hv']
  exact (h2 a ha (Φ₁ v)).2 _
 let setoid : Setoid (Fin L) :=
  {
   r := fun k l => IsoInv A (V k) (V l)
   iseqv := ⟨hiso_refl, fun h => hiso_symm h, fun h1 h2 => hiso_trans h1 h2⟩ }
 let Q := Quotient setoid
 let t := Fintype.card Q
 let eQ : Q ≃ Fin t := Fintype.equivFin Q
 let cls (i : Fin t) : Finset (Fin L) := univ.filter fun k => eQ (Quotient.mk setoid k) = i
 have hcls_nonempty : ∀ i : Fin t, (cls i).Nonempty := by
  intro i
  obtain ⟨k, hk⟩ := Quotient.exists_rep (eQ.symm i)
  refine ⟨k, mem_filter.mpr ⟨mem_univ k, ?_⟩⟩
  rw [hk, Equiv.apply_symm_apply]
 let s : Fin t → ℕ := fun i => (cls i).card
 have hs : ∀ i, 0 < s i := fun i => Finset.card_pos.mpr (hcls_nonempty i)
 let eC (i : Fin t) : Fin (s i) ≃ {k : Fin L // k ∈ cls i} :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe (cls i))).symm
 let idx (i : Fin t) (b : Fin (s i)) : Fin L := (eC i b).1
 let rep (i : Fin t) : Fin L := idx i ⟨0, hs i⟩
 let r : Fin t → ℕ := fun i => Module.finrank ℂ (V (rep i))
 have hr : ∀ i, 0 < r i := fun i =>
  Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr (hVirr (rep i)).1)
 have hidx_iso : ∀ (i : Fin t) (b : Fin (s i)), IsoInv A (V (rep i)) (V (idx i b)) := by
  intro i b
  have h1 : eQ (Quotient.mk setoid (rep i)) = i := (mem_filter.mp (eC i ⟨0, hs i⟩).2).2
  have h2 : eQ (Quotient.mk setoid (idx i b)) = i := (mem_filter.mp (eC i b).2).2
  exact Quotient.exact (eQ.injective (h1.trans h2.symm))
 let Φ (i : Fin t) (b : Fin (s i)) : V (rep i) ≃ₗᵢ[ℂ] V (idx i b) :=
  (hidx_iso i b).choose
 have hΦ (i : Fin t) (b : Fin (s i)) : ∀ a ∈ A, ∀ v : V (rep i),
   ∀ hv : CLM a v.1 ∈ V (rep i),
    (Φ i b ⟨CLM a v.1, hv⟩ : EuclideanSpace ℂ n) = CLM a (Φ i b v).1 :=
  fun a ha v hv => ((hidx_iso i b).choose_spec a ha v).2 hv
 let eb (i : Fin t) : OrthonormalBasis (Fin (r i)) ℂ (V (rep i)) :=
  stdOrthonormalBasis ℂ (V (rep i))
 let bvec : (Σ i : Fin t, Fin (r i) × Fin (s i)) → EuclideanSpace ℂ n :=
  fun ⟨i, a, b⟩ => (Φ i b (eb i a) : EuclideanSpace ℂ n)
 have hidx_inj : ∀ {i j : Fin t} {b : Fin (s i)} {d : Fin (s j)},
   idx i b = idx j d → i = j ∧ HEq b d := by
  intro i j b d heq
  have hi : eQ (Quotient.mk setoid (idx i b)) = i := (mem_filter.mp (eC i b).2).2
  have hj : eQ (Quotient.mk setoid (idx j d)) = j := (mem_filter.mp (eC j d).2).2
  have hij : i = j := by rw [← hi, heq, hj]
  subst hij
  have hsub : eC i b = eC i d := Subtype.ext heq
  exact ⟨rfl, heq_of_eq ((eC i).injective hsub)⟩
 have hbvec_orth : Orthonormal ℂ bvec := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, a, b⟩ ⟨j, c, d⟩
  by_cases hkl : idx i b = idx j d
  ·
   obtain ⟨rfl, hbd⟩ := hidx_inj hkl
   cases eq_of_heq hbd
   change ⟪(Φ i b (eb i a) : EuclideanSpace ℂ n), (Φ i b (eb i c) : EuclideanSpace ℂ n)⟫_ℂ = _
   rw [submodule_isometry_inner (Φ i b) (eb i a) (eb i c)]
   have horth : ⟪(eb i a : EuclideanSpace ℂ n), (eb i c : EuclideanSpace ℂ n)⟫_ℂ =
     if a = c then 1 else 0 := (orthonormal_iff_ite.mp (eb i).orthonormal) a c
   rw [horth]
   simp
  ·
   have hne : (⟨i, a, b⟩ : Σ i : Fin t, Fin (r i) × Fin (s i)) ≠ ⟨j, c, d⟩ := by
    intro heq; cases heq; exact hkl rfl
   rw [if_neg hne]
   exact hVorth (idx i b) (idx j d) hkl _ (Φ i b (eb i a)).2 _ (Φ j d (eb j c)).2
 have hbvec_span : Submodule.span ℂ (Set.range bvec) = ⊤ := by
  rw [← hVsup]
  apply le_antisymm
  · exact le_top.trans hVsup.symm.le
  ·
   refine iSup_le fun k => ?_
   let i := eQ (Quotient.mk setoid k)
   have hk : k ∈ cls i := mem_filter.mpr ⟨mem_univ k, rfl⟩
   let b := (eC i).symm ⟨k, hk⟩
   have hkb : idx i b = k := congrArg Subtype.val ((eC i).apply_symm_apply ⟨k, hk⟩)
   intro v hv
   let w : V (idx i b) := ⟨v, hkb ▸ hv⟩
   let u : V (rep i) := (Φ i b).symm w
   have hu : u = ∑ a : Fin (r i), ⟪eb i a, u⟫_ℂ • eb i a :=
    ((eb i).sum_repr' u).symm
   have hw : w = ∑ a : Fin (r i), ⟪eb i a, u⟫_ℂ • Φ i b (eb i a) := by
    calc
     w = Φ i b u := ((Φ i b).apply_symm_apply w).symm
     _ = Φ i b (∑ a : Fin (r i), ⟪eb i a, u⟫_ℂ • eb i a) := by rw [← hu]
     _ = ∑ a : Fin (r i), ⟪eb i a, u⟫_ℂ • Φ i b (eb i a) := by
        simp [map_sum, map_smul]
   have hv_eq : v = ∑ a : Fin (r i), ⟪eb i a, u⟫_ℂ • bvec ⟨i, a, b⟩ := by
    have := congrArg Subtype.val hw
    simpa [w, bvec] using this
   rw [hv_eq]
   exact Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, a, b⟩, rfl⟩)
 let U : Matrix n (Σ i : Fin t, Fin (r i) × Fin (s i)) ℂ :=
  fun x p => (bvec p).ofLp x
 have hU_star_mul : Uᴴ * U = 1 := by
  ext p q
  rw [mul_apply, Matrix.one_apply]
  have h1 : ∑ x : n, (Uᴴ) p x * U x q = ⟪bvec p, bvec q⟫_ℂ := by
   rw [inner_eq_star_dotProduct, dotProduct]
   refine sum_congr rfl fun x _ => ?_
   change star (U x p) * U x q = (bvec q).ofLp x * (starRingEnd ℂ) ((bvec p).ofLp x)
   rw [star_def, mul_comm]
  rw [h1, (orthonormal_iff_ite.mp hbvec_orth) p q]
 have hU_mul_star : U * Uᴴ = 1 := by
  have hvec : ∀ v : EuclideanSpace ℂ n,
    v = ∑ p, ⟪bvec p, v⟫_ℂ • bvec p := by
   intro v
   have hrepr : ∀ p, ⟪bvec p, v - ∑ q, ⟪bvec q, v⟫_ℂ • bvec q⟫_ℂ = 0 := by
    intro p
    rw [inner_sub_right, inner_sum]
    simp_rw [inner_smul_right, orthonormal_iff_ite.mp hbvec_orth]
    simp
   have horth_all : ∀ w ∈ Submodule.span ℂ (Set.range bvec),
     ⟪w, v - ∑ q, ⟪bvec q, v⟫_ℂ • bvec q⟫_ℂ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem u hu => rcases hu with ⟨p, rfl⟩; exact hrepr p
    | zero => simp
    | add u₁ u₂ _ _ h1 h2 => rw [inner_add_left, h1, h2, add_zero]
    | smul c u _ h1 => rw [inner_smul_left, h1, mul_zero]
   have hself := horth_all (v - ∑ q, ⟪bvec q, v⟫_ℂ • bvec q) (hbvec_span ▸ Submodule.mem_top)
   exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)
  ext x y
  have h1 := congrArg (fun w : EuclideanSpace ℂ n => w.ofLp x)
   (hvec (EuclideanSpace.single y (1 : ℂ)))
  rw [mul_apply, Matrix.one_apply]
  have hL : (EuclideanSpace.single y (1 : ℂ)).ofLp x = if x = y then 1 else 0 := by
   rw [PiLp.single_apply]
  have hR : (∑ p, ⟪bvec p, EuclideanSpace.single y (1 : ℂ)⟫_ℂ • bvec p).ofLp x =
    ∑ p, U x p * (Uᴴ) p y := by
   simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
   refine sum_congr rfl fun p _ => ?_
   rw [EuclideanSpace.inner_single_right, one_mul, mul_comm]
   change (bvec p).ofLp x * (starRingEnd ℂ) ((bvec p).ofLp y) = U x p * (Uᴴ) p y
   rw [ctA, star_def]
  rw [hL, hR] at h1
  exact h1.symm
 have hconj_entry : ∀ (X : Matrix n n ℂ) p q,
   (Uᴴ * X * U) p q = ⟪bvec p, CLM X (bvec q)⟫_ℂ := by
  intro X p q
  rw [inner_eq_star_dotProduct, dotProduct, mul_apply]
  have hL : ∑ y, (Uᴴ * X) p y * U y q = ∑ y, ∑ x, (Uᴴ) p x * X x y * U y q := by
   refine sum_congr rfl fun y _ => ?_
   rw [mul_apply, Finset.sum_mul]
  have hR : ∑ x, (CLM X (bvec q)).ofLp x * star (bvec p).ofLp x =
    ∑ x, ∑ y, X x y * (bvec q).ofLp y * star ((bvec p).ofLp x) := by
   refine sum_congr rfl fun x _ => ?_
   rw [ofLp_toEuclideanCLM, mulVec, dotProduct, Finset.sum_mul]
   simp only [Pi.star_apply]
  rw [hL, hR, sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [ctA]
  dsimp only [U]
  ring
 have hA_sub : ∀ a ∈ A, ∃ M, Uᴴ * a * U = bDA r s M := by
  intro a ha
  let M : (i : Fin t) → Matrix (Fin (r i)) (Fin (r i)) ℂ := fun i a' c' =>
   ⟪(eb i a' : EuclideanSpace ℂ n), CLM a (eb i c' : EuclideanSpace ℂ n)⟫_ℂ
  refine ⟨M, ?_⟩
  ext ⟨i, a', b⟩ ⟨j, c', d⟩
  rw [hconj_entry a ⟨i, a', b⟩ ⟨j, c', d⟩]
  have hact : CLM a (bvec ⟨j, c', d⟩) =
    (Φ j d ⟨CLM a (eb j c').1,
     (hVirr (rep j)).2.1 a ha (eb j c').1 (eb j c').2⟩ : EuclideanSpace ℂ n) :=
   (hΦ j d a ha (eb j c') _).symm
  rw [hact]
  by_cases hkl : idx i b = idx j d
  ·
   obtain ⟨rfl, hbd⟩ := hidx_inj hkl
   cases eq_of_heq hbd
   simp only [bDA, ↓reduceDIte, ↓reduceIte, M, bvec]
   exact submodule_isometry_inner (Φ i b) (eb i a') ⟨CLM a (eb i c').1, _⟩
  ·
   have h0 : ⟪bvec ⟨i, a', b⟩, (Φ j d ⟨CLM a (eb j c').1,
     (hVirr (rep j)).2.1 a ha (eb j c').1 (eb j c').2⟩ : EuclideanSpace ℂ n)⟫_ℂ = 0 :=
    hVorth (idx i b) (idx j d) hkl _ (Φ i b (eb i a')).2 _ (Φ j d _).2
   rw [h0]
   by_cases hij : i = j
   ·
    subst hij
    have hbd : b ≠ d := fun h => hkl (by rw [h])
    simp [bDA, hbd]
   · simp [bDA, hij]
 have hC_eq : ∀ X : Matrix n n ℂ, X ∈ comm A ↔ ∃ N, Uᴴ * X * U = bDC r s N := by
  intro X
  constructor
  ·
   intro hX
   have hblk : ∀ (i j : Fin t) (b : Fin (s i)) (d : Fin (s j)),
     ∃ c : ℂ, (i ≠ j → c = 0) ∧
      ∀ (a' : Fin (r i)) (c' : Fin (r j)),
       (Uᴴ * X * U) ⟨i, a', b⟩ ⟨j, c', d⟩ =
        if h : i = j then (if a' = (h ▸ c') then c else 0) else 0 := by
    intro i j b d
    let P : EuclideanSpace ℂ n →ₗ[ℂ] V (idx i b) :=
     (V (idx i b)).orthogonalProjectionOnto.toLinearMap
    let T : V (rep j) →ₗ[ℂ] V (rep i) :=
     (Φ i b).symm.toLinearEquiv.toLinearMap.comp
      (P.comp ((CLM X).toLinearMap.comp
       ((V (idx j d)).subtype.comp (Φ j d).toLinearEquiv.toLinearMap)))
    have hP_inv : ∀ a ∈ A, ∀ v : EuclideanSpace ℂ n,
      (P (CLM a v) : EuclideanSpace ℂ n) = CLM a (P v).1 := by
     intro a ha v
     have hsub : v = (P v : EuclideanSpace ℂ n) + (v - (P v : EuclideanSpace ℂ n)) := by abel
     have hv1 : CLM a (P v).1 ∈ V (idx i b) :=
      (hVirr (idx i b)).2.1 a ha (P v).1 (P v).2
     have hv2 : v - (P v : EuclideanSpace ℂ n) ∈ (V (idx i b))ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro w hw
      have h0 : ⟪v - (P v : EuclideanSpace ℂ n), w⟫_ℂ = 0 :=
       (V (idx i b)).starProjection_inner_eq_zero v w hw
      rw [← inner_conj_symm, h0, map_zero]
     have hv2' : CLM a (v - (P v : EuclideanSpace ℂ n)) ∈ (V (idx i b))ᗮ :=
      isInv_orthogonal (hVirr (idx i b)).2.1 a ha _ hv2
     have hP1 : (V (idx i b)).starProjection (CLM a (P v).1) = CLM a (P v).1 :=
      (V (idx i b)).starProjection_eq_self_iff.mpr hv1
     have hP2 : (V (idx i b)).starProjection (CLM a (v - (P v : EuclideanSpace ℂ n))) = 0 :=
      starProjection_eq_zero_of_mem_orthogonal (V (idx i b)) hv2'
     change (V (idx i b)).starProjection (CLM a v) = _
     conv_lhs => rw [hsub, map_add, map_add, hP1, hP2, add_zero]
    have hT_int : ∀ a (ha : a ∈ A) (v : V (rep j)),
      (T ⟨CLM a v.1, (hVirr (rep j)).2.1 a ha v.1 v.2⟩ : EuclideanSpace ℂ n) =
       CLM a (T v).1 := by
     intro a ha v
     have h1 : Φ j d ⟨CLM a v.1, (hVirr (rep j)).2.1 a ha v.1 v.2⟩ =
       ⟨CLM a (Φ j d v).1,
        (hVirr (idx j d)).2.1 a ha (Φ j d v).1 (Φ j d v).2⟩ :=
      Subtype.ext (hΦ j d a ha v _)
     have h2 : CLM X (CLM a (Φ j d v).1) = CLM a (CLM X (Φ j d v).1) := by
      have := congrArg (fun M => CLM M (Φ j d v).1) (hX a ha)
      simpa [map_mul] using this
     have h3 : P (CLM a (CLM X (Φ j d v).1)) =
       ⟨CLM a (P (CLM X (Φ j d v).1)).1,
        (hVirr (idx i b)).2.1 a ha _ (P _).2⟩ :=
      Subtype.ext (hP_inv a ha _)
     let u : V (rep i) := (Φ i b).symm (P (CLM X (Φ j d v).1))
     have h4 : (Φ i b).symm ⟨CLM a (P (CLM X (Φ j d v).1)).1,
       (hVirr (idx i b)).2.1 a ha _ (P _).2⟩ =
       ⟨CLM a u.1, (hVirr (rep i)).2.1 a ha u.1 u.2⟩ := by
      apply (Φ i b).injective
      apply Subtype.ext
      rw [LinearIsometryEquiv.apply_symm_apply, hΦ i b a ha u _]
      change CLM a (P (CLM X (Φ j d v).1)).1 = CLM a (Φ i b u).1
      rw [show Φ i b u = P (CLM X (Φ j d v).1) from LinearIsometryEquiv.apply_symm_apply _ _]
     have hTapp : ∀ w : V (rep j), T w = (Φ i b).symm (P (CLM X (Φ j d w).1)) := fun _ => rfl
     have hTeq : T ⟨CLM a v.1, (hVirr (rep j)).2.1 a ha v.1 v.2⟩ =
       ⟨CLM a (T v).1, (hVirr (rep i)).2.1 a ha (T v).1 (T v).2⟩ := by
      rw [hTapp, h1, h2, h3, h4]
      rfl
     exact congrArg Subtype.val hTeq
    have hT_inner : ∀ (a' : Fin (r i)) (c' : Fin (r j)),
      (Uᴴ * X * U) ⟨i, a', b⟩ ⟨j, c', d⟩ = ⟪eb i a', T (eb j c')⟫_ℂ := by
     intro a' c'
     rw [hconj_entry]
     have h1 : ⟪(eb i a' : EuclideanSpace ℂ n), (T (eb j c') : EuclideanSpace ℂ n)⟫_ℂ =
       ⟪(Φ i b (eb i a') : EuclideanSpace ℂ n),
        (P (CLM X (bvec ⟨j, c', d⟩)) : EuclideanSpace ℂ n)⟫_ℂ := by
      rw [← submodule_isometry_inner (Φ i b) (eb i a') (T (eb j c'))]
      have hTval : Φ i b (T (eb j c')) = P (CLM X (bvec ⟨j, c', d⟩)) := by
       simp [T, bvec]
      rw [hTval]
     change ⟪bvec ⟨i, a', b⟩, CLM X (bvec ⟨j, c', d⟩)⟫_ℂ =
      ⟪(eb i a' : EuclideanSpace ℂ n), (T (eb j c') : EuclideanSpace ℂ n)⟫_ℂ
     rw [h1]
     change ⟪(Φ i b (eb i a') : EuclideanSpace ℂ n), CLM X (bvec ⟨j, c', d⟩)⟫_ℂ =
      ⟪(Φ i b (eb i a') : EuclideanSpace ℂ n),
       (V (idx i b)).starProjection (CLM X (bvec ⟨j, c', d⟩))⟫_ℂ
     have horth := (V (idx i b)).starProjection_inner_eq_zero
      (CLM X (bvec ⟨j, c', d⟩)) (Φ i b (eb i a')).1 (Φ i b (eb i a')).2
     rw [← inner_conj_symm, inner_sub_right] at horth
     exact sub_eq_zero.mp ((map_eq_zero (starRingEnd ℂ)).mp horth)
    by_cases hij : i = j
    ·
     subst hij
     obtain ⟨c, hc⟩ := schur_end_eq_smul (hVirr (rep i)) T hT_int
     refine ⟨c, fun h => absurd rfl h, fun a' c' => ?_⟩
     rw [hT_inner, hc, LinearMap.smul_apply, LinearMap.id_apply]
     change ⟪(eb i a' : EuclideanSpace ℂ n), c • (eb i c' : EuclideanSpace ℂ n)⟫_ℂ = _
     rw [inner_smul_right]
     have horth : ⟪(eb i a' : EuclideanSpace ℂ n), (eb i c' : EuclideanSpace ℂ n)⟫_ℂ =
       if a' = c' then 1 else 0 := (orthonormal_iff_ite.mp (eb i).orthonormal) a' c'
     rw [horth]
     simp [mul_ite]
    ·
     have hT0 : T = 0 := by
      by_contra hne
      have hiso := isoInv_of_nonzero_intertwiner (hVirr (rep j)) (hVirr (rep i)) T hne hT_int
      have hq : Quotient.mk setoid (rep j) = Quotient.mk setoid (rep i) :=
       Quotient.sound hiso
      have hi : eQ (Quotient.mk setoid (rep i)) = i := (mem_filter.mp (eC i ⟨0, hs i⟩).2).2
      have hj : eQ (Quotient.mk setoid (rep j)) = j := (mem_filter.mp (eC j ⟨0, hs j⟩).2).2
      exact hij (hi.symm.trans (congrArg eQ hq.symm) |>.trans hj)
     refine ⟨0, fun _ => rfl, fun a' c' => ?_⟩
     rw [hT_inner, hT0]
     simp [hij]
   let N : (i : Fin t) → Matrix (Fin (s i)) (Fin (s i)) ℂ := fun i b d =>
    (hblk i i b d).choose
   refine ⟨N, ?_⟩
   ext ⟨i, a', b⟩ ⟨j, c', d⟩
   by_cases hij : i = j
   ·
    subst hij
    simpa [bDC, N] using (hblk i i b d).choose_spec.2 a' c'
   · simpa [bDC, hij] using (hblk i j b d).choose_spec.2 a' c'
  ·
   rintro ⟨N, hN⟩ a ha
   obtain ⟨M, hM⟩ := hA_sub a ha
   have hcomm : (Uᴴ * X * U) * (Uᴴ * a * U) = (Uᴴ * a * U) * (Uᴴ * X * U) := by
    rw [hN, hM]
    exact (blockDiagA_comm_blockDiagC r s M N).symm
   have hL : U * ((Uᴴ * X * U) * (Uᴴ * a * U)) * Uᴴ = X * a := by
    calc
     U * ((Uᴴ * X * U) * (Uᴴ * a * U)) * Uᴴ
      = (U * Uᴴ) * X * (U * Uᴴ) * a * (U * Uᴴ) := by simp [mma]
     _ = X * a := by rw [hU_mul_star]; simp
   have hR : U * ((Uᴴ * a * U) * (Uᴴ * X * U)) * Uᴴ = a * X := by
    calc
     U * ((Uᴴ * a * U) * (Uᴴ * X * U)) * Uᴴ
      = (U * Uᴴ) * a * (U * Uᴴ) * X * (U * Uᴴ) := by simp [mma]
     _ = a * X := by rw [hU_mul_star]; simp
   rw [← hL, ← hR, hcomm]
 refine ⟨⟨t, r, s, hr, hs, U, hU_star_mul, hU_mul_star, fun X => ?_⟩⟩
 constructor
 · exact hA_sub X
 ·
  rintro ⟨M, hM⟩
  rw [← bicommutant_eq A, mem_commutant]
  intro Y hY
  obtain ⟨N, hN⟩ := (hC_eq Y).mp hY
  have hcomm : (Uᴴ * X * U) * (Uᴴ * Y * U) = (Uᴴ * Y * U) * (Uᴴ * X * U) := by
   rw [hM, hN]; exact blockDiagA_comm_blockDiagC r s M N
  have hL : U * ((Uᴴ * X * U) * (Uᴴ * Y * U)) * Uᴴ = X * Y := by
   calc
    U * ((Uᴴ * X * U) * (Uᴴ * Y * U)) * Uᴴ
     = (U * Uᴴ) * X * (U * Uᴴ) * Y * (U * Uᴴ) := by simp [mma]
    _ = X * Y := by rw [hU_mul_star]; simp
  have hR : U * ((Uᴴ * Y * U) * (Uᴴ * X * U)) * Uᴴ = Y * X := by
   calc
    U * ((Uᴴ * Y * U) * (Uᴴ * X * U)) * Uᴴ
     = (U * Uᴴ) * Y * (U * Uᴴ) * X * (U * Uᴴ) := by simp [mma]
    _ = Y * X := by rw [hU_mul_star]; simp
  rw [← hL, ← hR, hcomm]
end ExistsBlockDecomp
end BDec
/- ### 5. Finite Heisenberg-Weyl unitary 1-design and polar decomposition -/
section OneDesign
abbrev HWI (p : ℕ) := Fin (2 * p) × Fin p × Fin p
lemma nat_add_mod_cancel {p x g : ℕ} (hx : x < p) (hg : g < p) :
  ((x + g) % p + (p - g)) % p = x := by
 rw [Nat.mod_add_mod]
 have h : x + g + (p - g) = x + p := by omega
 rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hx]
lemma nat_mod_add_assoc {p a b c : ℕ} :
  ((a + b) % p + c) % p = (a + (b + c) % p) % p := by
 rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
def hwM (p : ℕ) (g : HWI p) : Matrix (Fin p) (Fin p) ℂ :=
 fun x y =>
  if (x.val + g.2.2.val) % p = y.val then
   exp (2 * Real.pi * Complex.I *
    ((g.1.val : ℂ) / (2 * p : ℂ) + (g.2.1.val * x.val : ℂ) / (p : ℂ)))
  else 0
lemma hwMat_unitary {p : ℕ} (hp : 0 < p) (g : HWI p) :
  (hwM p g)ᴴ * hwM p g = 1 ∧ hwM p g * (hwM p g)ᴴ = 1 := by
 have hnorm_exp : ∀ θ : ℝ, star (exp (Complex.I * (θ : ℂ))) *
   exp (Complex.I * (θ : ℂ)) = 1 := by
  intro θ
  rw [star_def, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, conj_ofReal, ← exp_add]
  ring_nf
  exact Complex.exp_zero
 constructor
 ·
  ext y z
  rw [mul_apply, Matrix.one_apply]
  let x₀ : Fin p := ⟨(y.val + (p - g.2.2.val)) % p, Nat.mod_lt _ hp⟩
  have hx₀ : (x₀.val + g.2.2.val) % p = y.val := by
   have hge : g.2.2.val ≤ p := le_of_lt g.2.2.isLt
   have h1 : y.val + (p - g.2.2.val) + g.2.2.val = y.val + p := by omega
   simp only [x₀]
   rw [Nat.mod_add_mod, h1, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]
  rw [sum_eq_single x₀]
  ·
   simp only [ctA, hwM, hx₀, ↓reduceIte]
   by_cases hyz : y = z
   ·
    subst hyz
    simp only [↓reduceIte]
    have hθ : 2 * ↑Real.pi * Complex.I *
      (↑g.1.val / (2 * ↑p) + ↑g.2.1.val * ↑x₀.val / ↑p) =
      Complex.I * ((2 * Real.pi * (g.1.val / (2 * (p : ℝ)) + g.2.1.val * x₀.val / p) : ℝ) : ℂ) := by
     push_cast; ring
    rw [hθ]
    exact hnorm_exp _
   ·
    have hne : ¬ (y.val = z.val) := fun h => hyz (Fin.ext h)
    simp [hne, hyz]
  ·
   intro x _ hxx₀
   have hne : (x.val + g.2.2.val) % p ≠ y.val := by
    intro heq
    apply hxx₀
    apply Fin.ext
    have h := nat_add_mod_cancel x.isLt g.2.2.isLt
    rw [heq] at h
    exact h.symm
   simp [hwM, hne]
  · intro h; exact absurd (mem_univ x₀) h
 ·
  ext x z
  rw [mul_apply, Matrix.one_apply]
  let y₀ : Fin p := ⟨(x.val + g.2.2.val) % p, Nat.mod_lt _ hp⟩
  rw [sum_eq_single y₀]
  ·
   simp only [ctA, hwM, y₀, ↓reduceIte]
   by_cases hxz : x = z
   ·
    subst hxz
    simp only [↓reduceIte]
    have hθ : 2 * ↑Real.pi * Complex.I *
      (↑g.1.val / (2 * ↑p) + ↑g.2.1.val * ↑x.val / ↑p) =
      Complex.I * ((2 * Real.pi * (g.1.val / (2 * (p : ℝ)) + g.2.1.val * x.val / p) : ℝ) : ℂ) := by
     push_cast; ring
    rw [hθ, mul_comm]
    exact hnorm_exp _
   ·
    have hne : (z.val + g.2.2.val) % p ≠ (x.val + g.2.2.val) % p := by
     intro heq
     apply hxz
     apply Fin.ext
     have hz := nat_add_mod_cancel z.isLt g.2.2.isLt
     have hx := nat_add_mod_cancel x.isLt g.2.2.isLt
     rw [heq] at hz
     exact hx.symm.trans hz
    simp [hne, hxz]
  ·
   intro y _ hyy₀
   have hne : (x.val + g.2.2.val) % p ≠ y.val := fun h => hyy₀ (Fin.ext h).symm
   simp [hwM, hne]
  · intro h; exact absurd (mem_univ y₀) h
def hwMul {p : ℕ} (hp : 0 < p) (g₁ g₂ : HWI p) : HWI p :=
 (⟨(g₁.1.val + g₂.1.val + 2 * g₂.2.1.val * g₁.2.2.val) % (2 * p), Nat.mod_lt _ (by omega)⟩,
  ⟨(g₁.2.1.val + g₂.2.1.val) % p, Nat.mod_lt _ hp⟩,
  ⟨(g₁.2.2.val + g₂.2.2.val) % p, Nat.mod_lt _ hp⟩)
lemma exp_two_pi_I_nat_mul (k : ℕ) :
  exp (2 * Real.pi * Complex.I * (k : ℂ)) = 1 := by
 have h : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) = (k : ℤ) * (2 * Real.pi * Complex.I) := by
  push_cast; ring
 rw [h, Complex.exp_int_mul_two_pi_mul_I]
lemma exp_mod_eq {m : ℕ} (hm : 0 < m) (a : ℕ) :
  exp (2 * Real.pi * Complex.I * ((a % m : ℕ) : ℂ) / (m : ℂ)) =
   exp (2 * Real.pi * Complex.I * (a : ℂ) / (m : ℂ)) := by
 have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
 have hdiv : a = a % m + m * (a / m) := (Nat.mod_add_div a m).symm
 conv_rhs => rw [hdiv]
 push_cast
 have hsplit : 2 * (Real.pi : ℂ) * Complex.I * ((a % m : ℕ) + (m : ℂ) * (a / m : ℕ)) / (m : ℂ) =
   2 * Real.pi * Complex.I * ((a % m : ℕ) : ℂ) / (m : ℂ) +
    2 * Real.pi * Complex.I * ((a / m : ℕ) : ℂ) := by
  field_simp [hm0]
 rw [hsplit, exp_add, exp_two_pi_I_nat_mul, mul_one]
lemma hwMat_mul {p : ℕ} (hp : 0 < p) (g₁ g₂ : HWI p) :
  hwM p g₁ * hwM p g₂ = hwM p (hwMul hp g₁ g₂) := by
 have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hp)
 ext x y
 rw [mul_apply]
 let z₀ : Fin p := ⟨(x.val + g₁.2.2.val) % p, Nat.mod_lt _ hp⟩
 rw [sum_eq_single z₀]
 ·
  dsimp only [hwM, hwMul, z₀]
  simp only [↓reduceIte]
  have hmod_iff : ((x.val + g₁.2.2.val) % p + g₂.2.2.val) % p = y.val ↔
    (x.val + (g₁.2.2.val + g₂.2.2.val) % p) % p = y.val := by
   rw [nat_mod_add_assoc]
  by_cases hxy : (x.val + (g₁.2.2.val + g₂.2.2.val) % p) % p = y.val
  ·
   simp only [hxy, hmod_iff.mpr hxy, ↓reduceIte]
   rw [← exp_add]
   have h1 : 2 * (Real.pi : ℂ) * Complex.I *
     (((g₁.1.val + g₂.1.val + 2 * g₂.2.1.val * g₁.2.2.val) % (2 * p) : ℕ) / (2 * (p : ℂ)) +
      ((g₁.2.1.val + g₂.2.1.val) % p : ℕ) * (x.val : ℂ) / (p : ℂ)) =
     2 * Real.pi * Complex.I *
      (((g₁.1.val + g₂.1.val + 2 * g₂.2.1.val * g₁.2.2.val) % (2 * p) : ℕ) : ℂ) / ((2 * p : ℕ) : ℂ) +
     2 * Real.pi * Complex.I *
      ((((g₁.2.1.val + g₂.2.1.val) % p) * x.val : ℕ) : ℂ) / (p : ℂ) := by
    push_cast; ring
   have h2 : 2 * (Real.pi : ℂ) * Complex.I *
     ((g₁.1.val : ℂ) / (2 * p) + (g₁.2.1.val : ℂ) * (x.val : ℂ) / p) +
     2 * Real.pi * Complex.I *
      ((g₂.1.val : ℂ) / (2 * p) + (g₂.2.1.val : ℂ) * ((x.val + g₁.2.2.val) % p : ℕ) / p) =
     2 * Real.pi * Complex.I * (((g₁.1.val + g₂.1.val : ℕ) : ℂ)) / ((2 * p : ℕ) : ℂ) +
     2 * Real.pi * Complex.I *
      ((g₁.2.1.val * x.val + g₂.2.1.val * ((x.val + g₁.2.2.val) % p) : ℕ) : ℂ) / (p : ℂ) := by
    push_cast; ring
   rw [h1, h2, exp_add, exp_add, exp_mod_eq (by omega : 0 < 2 * p)]
   have hmod2 : ((g₁.2.1.val + g₂.2.1.val) % p * x.val) % p =
     ((g₁.2.1.val + g₂.2.1.val) * x.val) % p := by simp [Nat.mul_mod]
   rw [← exp_mod_eq hp (((g₁.2.1.val + g₂.2.1.val) % p) * x.val), hmod2, exp_mod_eq hp]
   have hmod3 : (g₁.2.1.val * x.val + g₂.2.1.val * ((x.val + g₁.2.2.val) % p)) % p =
     (g₁.2.1.val * x.val + g₂.2.1.val * (x.val + g₁.2.2.val)) % p := by
    simp [Nat.add_mod, Nat.mul_mod]
   rw [← exp_mod_eq hp (g₁.2.1.val * x.val + _), hmod3, exp_mod_eq hp]
   rw [← exp_add, ← exp_add]
   congr 1
   push_cast
   field_simp [hp0]
   ring
  · simp only [hxy, mt hmod_iff.mp hxy, ↓reduceIte, mul_zero]
 ·
  intro z _ hzz₀
  have hne : (x.val + g₁.2.2.val) % p ≠ z.val := fun h => hzz₀ (Fin.ext h).symm
  simp [hwM, hne]
 · intro h; exact absurd (mem_univ z₀) h
lemma hwMul_bijective_left {p : ℕ} (hp : 0 < p) (g₁ : HWI p) :
  Function.Bijective (fun g₂ : HWI p => hwMul hp g₁ g₂) := by
 refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, rfl⟩
 rintro ⟨c₂, a₂, b₂⟩ ⟨c₂', a₂', b₂'⟩ heq
 have hc : (g₁.1.val + c₂.val + 2 * a₂.val * g₁.2.2.val) % (2 * p) =
   (g₁.1.val + c₂'.val + 2 * a₂'.val * g₁.2.2.val) % (2 * p) :=
  congrArg (fun x => x.1.val) heq
 have ha : (g₁.2.1.val + a₂.val) % p = (g₁.2.1.val + a₂'.val) % p :=
  congrArg (fun x => x.2.1.val) heq
 have hb : (g₁.2.2.val + b₂.val) % p = (g₁.2.2.val + b₂'.val) % p :=
  congrArg (fun x => x.2.2.val) heq
 have ha_eq : a₂ = a₂' := by
  apply Fin.ext
  have h1 := nat_add_mod_cancel a₂.isLt g₁.2.1.isLt
  have h2 := nat_add_mod_cancel a₂'.isLt g₁.2.1.isLt
  rw [Nat.add_comm a₂.val, ha, Nat.add_comm g₁.2.1.val] at h1
  exact h1.symm.trans h2
 subst ha_eq
 have hb_eq : b₂ = b₂' := by
  apply Fin.ext
  have h1 := nat_add_mod_cancel b₂.isLt g₁.2.2.isLt
  have h2 := nat_add_mod_cancel b₂'.isLt g₁.2.2.isLt
  rw [Nat.add_comm b₂.val, hb, Nat.add_comm g₁.2.2.val] at h1
  exact h1.symm.trans h2
 subst hb_eq
 have hc_eq : c₂ = c₂' := by
  apply Fin.ext
  let k := (g₁.1.val + 2 * a₂.val * g₁.2.2.val) % (2 * p)
  have hk : k < 2 * p := Nat.mod_lt _ (by omega)
  have h1 : (c₂.val + k) % (2 * p) = (c₂'.val + k) % (2 * p) := by
   have hL : (g₁.1.val + c₂.val + 2 * a₂.val * g₁.2.2.val) % (2 * p) = (c₂.val + k) % (2 * p) := by
    rw [Nat.add_mod_mod]
    congr 1; ring
   have hR : (g₁.1.val + c₂'.val + 2 * a₂.val * g₁.2.2.val) % (2 * p) = (c₂'.val + k) % (2 * p) := by
    rw [Nat.add_mod_mod]
    congr 1; ring
   rw [← hL, ← hR]; exact hc
  have h2 := nat_add_mod_cancel c₂.isLt hk
  have h3 := nat_add_mod_cancel c₂'.isLt hk
  rw [h1] at h2
  exact h2.symm.trans h3
 subst hc_eq
 rfl
lemma sum_exp_roots_of_unity {m : ℕ} (hm : 0 < m) (k : ℤ) :
  ∑ j : Fin m, exp (2 * Real.pi * Complex.I * (j.val : ℂ) * (k : ℂ) / (m : ℂ)) =
   if (m : ℤ) ∣ k then (m : ℂ) else 0 := by
 have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
 let ζ : ℂ := exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ))
 have hterm : ∀ j : Fin m,
   exp (2 * Real.pi * Complex.I * (j.val : ℂ) * (k : ℂ) / (m : ℂ)) = ζ ^ j.val := by
  intro j
  rw [← Complex.exp_nat_mul]
  congr 1; ring
 simp_rw [hterm]
 rw [Fin.sum_univ_eq_sum_range (fun j => ζ ^ j) m]
 by_cases hdvd : (m : ℤ) ∣ k
 ·
  obtain ⟨q, rfl⟩ := hdvd
  have hζ : ζ = 1 := by
   have : 2 * (Real.pi : ℂ) * Complex.I * ((m * q : ℤ) : ℂ) / (m : ℂ) =
     (q : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; field_simp [hm0]
   simp only [ζ, this, Complex.exp_int_mul_two_pi_mul_I]
  simp [hζ]
 ·
  rw [if_neg hdvd]
  have hζ_ne : ζ ≠ 1 := by
   intro h1
   rw [Complex.exp_eq_one_iff] at h1
   obtain ⟨q, hq⟩ := h1
   have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
   have hq' : (k : ℂ) / (m : ℂ) = (q : ℂ) := by
    apply mul_left_cancel₀ hpi
    have : 2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) / (m : ℂ)) =
      2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ) := by ring
    rw [this, hq]; ring
   have hkm : (k : ℂ) = (m : ℂ) * (q : ℂ) := by
    rw [← hq', mul_div_cancel₀ _ hm0]
   have hkm_int : k = (m : ℤ) * q := by exact_mod_cast hkm
   exact hdvd ⟨q, hkm_int⟩
  have hζm : ζ ^ m = 1 := by
   rw [← Complex.exp_nat_mul]
   have : (m : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) =
     (k : ℂ) * (2 * Real.pi * Complex.I) := by
    field_simp [hm0]
   rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hgeom := geom_sum_mul ζ m
  rw [hζm, sub_self] at hgeom
  exact mul_right_cancel₀ (sub_ne_zero.mpr hζ_ne) (by simpa using hgeom)
lemma hwMat_first_moment {p : ℕ} (hp : 0 < p) (x y : Fin p) :
  ∑ g : HWI p, hwM p g x y = 0 := by
 rw [sum_prod_type]
 rw [sum_comm]
 refine sum_eq_zero fun ab _ => ?_
 unfold hwM
 by_cases hxy : (x.val + ab.2.val) % p = y.val
 ·
  simp only [hxy, ↓reduceIte]
  have hfac : ∀ c : Fin (2 * p),
    exp (2 * Real.pi * Complex.I *
     ((c.val : ℂ) / (2 * p : ℂ) + (ab.1.val * x.val : ℂ) / (p : ℂ))) =
    exp (2 * Real.pi * Complex.I * (c.val : ℂ) * ((1 : ℤ) : ℂ) / ((2 * p : ℕ) : ℂ)) *
     exp (2 * Real.pi * Complex.I * ((ab.1.val * x.val : ℂ) / (p : ℂ))) := by
   intro c
   rw [← exp_add]
   congr 1; push_cast; ring
  simp_rw [hfac, ← Finset.sum_mul]
  rw [sum_exp_roots_of_unity (by omega : 0 < 2 * p) 1]
  have hndvd : ¬ ((2 * p : ℕ) : ℤ) ∣ (1 : ℤ) := by
   intro h
   have hle : ((2 * p : ℕ) : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) h
   omega
  rw [if_neg hndvd, zero_mul]
 · simp [hxy]
lemma hwMat_second_moment {p : ℕ} (hp : 0 < p) (x y z w : Fin p) :
  ∑ g : HWI p, hwM p g x y * star (hwM p g z w) =
   if x = z ∧ y = w then ((2 * p * p : ℕ) : ℂ) else 0 := by
 have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hp)
 rw [sum_prod_type]
 simp_rw [sum_prod_type]
 have hinner : ∀ (c : Fin (2 * p)) (a : Fin p) (b : Fin p),
   hwM p (c, a, b) x y * star (hwM p (c, a, b) z w) =
   if (x.val + b.val) % p = y.val ∧ (z.val + b.val) % p = w.val then
    exp (2 * Real.pi * Complex.I * (a.val : ℂ) * (((x.val : ℤ) - (z.val : ℤ)) : ℂ) / (p : ℂ))
   else 0 := by
  intro c a b
  dsimp only [hwM]
  by_cases h1 : (x.val + b.val) % p = y.val
  ·
   by_cases h2 : (z.val + b.val) % p = w.val
   ·
    simp only [h1, h2, and_self, ↓reduceIte]
    rw [star_def, ← Complex.exp_conj, ← exp_add]
    congr 1
    simp only [map_mul, map_add, map_div₀, conj_ofReal, Complex.conj_I, map_natCast,
     map_ofNat]
    push_cast; ring
   · simp [h1, h2]
  · simp [h1]
 simp_rw [hinner]
 rw [sum_const, card_univ, card_fin, nsmul_eq_mul]
 rw [sum_comm]
 let b₀ : Fin p := ⟨(y.val + p - x.val) % p, Nat.mod_lt _ hp⟩
 have hb₀ : (x.val + b₀.val) % p = y.val := by
  have h1 : x.val + (y.val + p - x.val) = y.val + p := by omega
  calc
   (x.val + b₀.val) % p
    = (x.val + (y.val + p - x.val)) % p := by simp [b₀, Nat.add_mod]
   _ = (y.val + p) % p := by rw [h1]
   _ = y.val := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]
 rw [sum_eq_single b₀]
 ·
  by_cases hzw : (z.val + b₀.val) % p = w.val
  ·
   simp only [hb₀, hzw, and_self, ↓reduceIte]
   simp_rw [← Int.cast_sub]
   rw [sum_exp_roots_of_unity hp ((x.val : ℤ) - (z.val : ℤ))]
   have hdvd_iff : ((p : ℤ) ∣ (x.val : ℤ) - (z.val : ℤ)) ↔ x = z := by
    constructor
    ·
     rintro ⟨q, hq⟩
     have hlt1 : (x.val : ℤ) < p := Int.ofNat_lt.mpr x.isLt
     have hlt2 : (z.val : ℤ) < p := Int.ofNat_lt.mpr z.isLt
     have hq0 : q = 0 := by nlinarith
     rw [hq0, mul_zero] at hq
     have : x.val = z.val := by omega
     exact Fin.ext this
    · rintro rfl; simp
   by_cases hxz : x = z
   ·
    subst hxz
    have hyw : y = w := Fin.ext (hb₀.symm.trans hzw)
    simp only [hdvd_iff.mpr rfl, ↓reduceIte, hyw, and_self]
    push_cast; ring
   · simp [hdvd_iff, hxz]
  ·
   simp only [hb₀, hzw, and_false, ↓reduceIte, sum_const_zero, mul_zero]
   by_cases hxz : x = z
   ·
    subst hxz
    have hyw : y ≠ w := fun h => hzw (h ▸ hb₀)
    simp [hyw]
   · simp [hxz]
 ·
  intro b _ hbb₀
  have hne : (x.val + b.val) % p ≠ y.val := by
   intro heq
   apply hbb₀
   apply Fin.ext
   have hge : x.val ≤ p := le_of_lt x.isLt
   have h1 : ((x.val + b.val) % p + (p - x.val)) % p = (y.val + (p - x.val)) % p := by rw [heq]
   rw [Nat.mod_add_mod] at h1
   have hL : x.val + b.val + (p - x.val) = b.val + p := by omega
   have hR : y.val + (p - x.val) = y.val + p - x.val := by omega
   rw [hL, hR, Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt] at h1
   exact h1
  simp [hne]
 · intro h; exact absurd (mem_univ b₀) h
/- Block unitary 1-design for any BDec A -/
abbrev BHW {n : Type*} [Fintype n] [DecidableEq n]
  {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A) :=
 (i : Fin bd.t) → HWI (bd.r i)
def bHW {n : Type*} [Fintype n] [DecidableEq n]
  {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A) (g : BHW bd) : Matrix n n ℂ :=
 bd.U * bDA bd.r bd.s (fun i => hwM (bd.r i) (g i)) * bd.Uᴴ
lemma blockHWMat_mem {n : Type*} [Fintype n] [DecidableEq n]
  {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A) (g : BHW bd) :
  bHW bd g ∈ A := by
 rw [bd.mem_iff]
 refine ⟨fun i => hwM (bd.r i) (g i), ?_⟩
 simp only [bHW]
 calc
  bd.Uᴴ * (bd.U * bDA bd.r bd.s (fun i => hwM (bd.r i) (g i)) * bd.Uᴴ) * bd.U
   = (bd.Uᴴ * bd.U) * bDA bd.r bd.s (fun i => hwM (bd.r i) (g i)) * (bd.Uᴴ * bd.U) := by
     simp only [mma]
  _ = bDA bd.r bd.s (fun i => hwM (bd.r i) (g i)) := by
     rw [bd.U_star_mul, m1m, mm1]
lemma bHW_u {n : Type*} [Fintype n] [DecidableEq n]
  {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A) (g : BHW bd) :
  bHW bd g ∈ unitaryGroup n ℂ := by
 rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
 simp only [bHW, ctM, ctct,
  blockDiagA_conjTranspose]
 have h1 : (fun i : Fin bd.t => (hwM (bd.r i) (g i))ᴴ * hwM (bd.r i) (g i)) = fun _ => 1 :=
  funext fun i => (hwMat_unitary (bd.hr i) (g i)).1
 calc
  bd.U * (bDA bd.r bd.s (fun i => (hwM (bd.r i) (g i))ᴴ) * bd.Uᴴ) *
   (bd.U * bDA bd.r bd.s (fun i => hwM (bd.r i) (g i)) * bd.Uᴴ)
   = bd.U * (bDA bd.r bd.s (fun i => (hwM (bd.r i) (g i))ᴴ) *
     ((bd.Uᴴ * bd.U) * bDA bd.r bd.s (fun i => hwM (bd.r i) (g i)))) * bd.Uᴴ := by
     simp only [mma]
  _ = bd.U * bDA bd.r bd.s (fun i => (hwM (bd.r i) (g i))ᴴ * hwM (bd.r i) (g i)) * bd.Uᴴ := by
     rw [bd.U_star_mul, m1m, blockDiagA_mul]
  _ = bd.U * bDA bd.r bd.s (fun _ => 1) * bd.Uᴴ := by rw [h1]
  _ = 1 := by rw [blockDiagA_one, mm1, bd.U_mul_star]
lemma blockHWMat_mul {n : Type*} [Fintype n] [DecidableEq n]
  {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A) (g₁ g₂ : BHW bd) :
  bHW bd g₁ * bHW bd g₂ =
   bHW bd (fun i => hwMul (bd.hr i) (g₁ i) (g₂ i)) := by
 simp only [bHW]
 have h1 : (fun i : Fin bd.t => hwM (bd.r i) (g₁ i) * hwM (bd.r i) (g₂ i)) =
   fun i => hwM (bd.r i) (hwMul (bd.hr i) (g₁ i) (g₂ i)) :=
  funext fun i => hwMat_mul (bd.hr i) (g₁ i) (g₂ i)
 calc
  (bd.U * bDA bd.r bd.s (fun i => hwM (bd.r i) (g₁ i)) * bd.Uᴴ) *
   (bd.U * bDA bd.r bd.s (fun i => hwM (bd.r i) (g₂ i)) * bd.Uᴴ)
   = bd.U * (bDA bd.r bd.s (fun i => hwM (bd.r i) (g₁ i)) *
     ((bd.Uᴴ * bd.U) * bDA bd.r bd.s (fun i => hwM (bd.r i) (g₂ i)))) * bd.Uᴴ := by
     simp only [mma]
  _ = bd.U * bDA bd.r bd.s (fun i => hwM (bd.r i) (g₁ i) * hwM (bd.r i) (g₂ i)) * bd.Uᴴ := by
     rw [bd.U_star_mul, m1m, blockDiagA_mul]
  _ = bd.U * bDA bd.r bd.s (fun i => hwM (bd.r i) (hwMul (bd.hr i) (g₁ i) (g₂ i))) * bd.Uᴴ := by
     rw [h1]
lemma blockHW_card_pos {n : Type*} [Fintype n] [DecidableEq n]
  {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A) :
  0 < Fintype.card (BHW bd) := by
 have : Nonempty (BHW bd) :=
  ⟨fun i => (⟨0, by have := bd.hr i; omega⟩, ⟨0, bd.hr i⟩, ⟨0, bd.hr i⟩)⟩
 exact Fintype.card_pos
lemma blockHW_span_eq {n : Type*} [Fintype n] [DecidableEq n]
  {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A) {a : Matrix n n ℂ} (ha : a ∈ A) :
  ∃ coeff : BHW bd → ℂ, a = ∑ g : BHW bd, coeff g • bHW bd g := by
 obtain ⟨M, hM⟩ := (bd.mem_iff a).mp ha
 have hcard : ∀ i : Fin bd.t, Fintype.card (HWI (bd.r i)) = 2 * bd.r i * bd.r i * bd.r i := by
  intro i; simp only [Fintype.card_prod, card_fin]; ring
 have hsingle : ∀ (i : Fin bd.t),
   M i = (((2 * bd.r i * bd.r i : ℕ) : ℂ)⁻¹) •
    ∑ u : HWI (bd.r i), ((hwM (bd.r i) u)ᴴ * M i).trace • hwM (bd.r i) u := by
  intro i
  have h2r0 : ((2 * bd.r i * bd.r i : ℕ) : ℂ) ≠ 0 :=
   Nat.cast_ne_zero.mpr (by have := bd.hr i; positivity)
  ext x y
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.trace, Matrix.diag_apply,
   mul_apply, ctA]
  have hsum : (∑ u : HWI (bd.r i),
    (∑ z : Fin (bd.r i), ∑ w : Fin (bd.r i), star (hwM (bd.r i) u w z) * M i w z) *
     hwM (bd.r i) u x y) =
    ∑ z : Fin (bd.r i), ∑ w : Fin (bd.r i),
     M i w z * ∑ u : HWI (bd.r i), hwM (bd.r i) u x y * star (hwM (bd.r i) u w z) := by
   simp_rw [Finset.sum_mul]
   rw [sum_comm]
   refine sum_congr rfl fun z _ => ?_
   rw [sum_comm]
   refine sum_congr rfl fun w _ => ?_
   rw [Finset.mul_sum]
   refine sum_congr rfl fun u _ => by ring
  rw [hsum]
  simp_rw [hwMat_second_moment (bd.hr i)]
  rw [sum_eq_single y]
  ·
   rw [sum_eq_single x]
   ·
    simp only [and_self, ↓reduceIte]
    rw [mul_left_comm, inv_mul_cancel₀ h2r0, mul_one]
   · intro w _ hwx; simp [hwx.symm]
   · intro h; exact absurd (mem_univ x) h
  ·
   intro z _ hzy
   exact sum_eq_zero fun w _ => by simp [hzy.symm]
  · intro h; exact absurd (mem_univ y) h
 let N_card : ℂ := (Fintype.card (BHW bd) : ℂ)
 have hN0 : N_card ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (blockHW_card_pos bd))
 let coeff : BHW bd → ℂ := fun g =>
  N_card⁻¹ * ∑ i : Fin bd.t, (bd.r i : ℂ) * ((hwM (bd.r i) (g i))ᴴ * M i).trace
 refine ⟨coeff, ?_⟩
 have hblock : bDA bd.r bd.s M =
   ∑ g : BHW bd, coeff g • bDA bd.r bd.s (fun i => hwM (bd.r i) (g i)) := by
  ext ⟨j, x, b⟩ ⟨k, y, d⟩
  by_cases hjk : j = k
  ·
   subst hjk
   by_cases hbd : b = d
   ·
    subst hbd
    simp only [bDA, ↓reduceDIte, ↓reduceIte, Matrix.sum_apply, Matrix.smul_apply,
     smul_eq_mul, coeff]
    simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
    rw [sum_comm]
    rw [sum_eq_single j]
    ·
     have hsplit : ∀ f : HWI (bd.r j) → ℂ,
       ∑ g : BHW bd, f (g j) =
        ((Fintype.card (BHW bd) / Fintype.card (HWI (bd.r j)) : ℕ) : ℂ) *
         ∑ u : HWI (bd.r j), f u := by
      intro f
      let ePi : BHW bd ≃ HWI (bd.r j) × ((i : {i : Fin bd.t // i ≠ j}) → HWI (bd.r i.1)) :=
       {
        toFun := fun g => (g j, fun i => g i.1)
        invFun := fun p i => if h : i = j then h ▸ p.1 else p.2 ⟨i, h⟩
        left_inv := fun g => by funext i; by_cases h : i = j <;> simp [h]; subst h; rfl
        right_inv := fun p => by
         apply Prod.ext
         · simp
         · funext i; simp [i.2] }
      rw [← Equiv.sum_comp ePi.symm, sum_prod_type]
      have hsimp : ∀ u : HWI (bd.r j), ∀ rest : ((i : {i : Fin bd.t // i ≠ j}) → HWI (bd.r i.1)),
        f (ePi.symm (u, rest) j) = f u := fun u rest => by simp [ePi]
      simp_rw [hsimp, sum_const, card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      congr 1
      have hdiv : Fintype.card (BHW bd) =
        Fintype.card ((i : {i : Fin bd.t // i ≠ j}) → HWI (bd.r i.1)) *
         Fintype.card (HWI (bd.r j)) := by
       rw [Fintype.card_congr ePi, Fintype.card_prod, mul_comm]
      have hpos : 0 < Fintype.card (HWI (bd.r j)) := by
       rw [hcard j]; have := bd.hr j; positivity
      rw [hdiv, Nat.mul_div_cancel _ hpos]
     simp_rw [mul_assoc]
     rw [← Finset.mul_sum, hsplit (fun u => ((hwM (bd.r j) u)ᴴ * M j).trace * hwM (bd.r j) u x y)]
     have hMj := congrFun (congrFun (hsingle j) x) y
     simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul] at hMj
     rw [hMj]
     have hdiv_cast : ((Fintype.card (BHW bd) / Fintype.card (HWI (bd.r j)) : ℕ) : ℂ) =
       N_card / (Fintype.card (HWI (bd.r j)) : ℂ) := by
      have hdvd : Fintype.card (HWI (bd.r j)) ∣ Fintype.card (BHW bd) := by
       rw [Fintype.card_pi]
       exact Finset.dvd_prod_of_mem _ (mem_univ j)
      rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (by rw [hcard j]; have := bd.hr j; positivity))]
     rw [hdiv_cast, hcard j]
     have hrj0 : (bd.r j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (bd.hr j))
     push_cast
     field_simp [hN0, hrj0]
    ·
     intro i _ hij
     let ePi : BHW bd ≃ HWI (bd.r j) × ((k : {k : Fin bd.t // k ≠ j}) → HWI (bd.r k.1)) :=
      {
       toFun := fun g => (g j, fun k => g k.1)
       invFun := fun p k => if h : k = j then h ▸ p.1 else p.2 ⟨k, h⟩
       left_inv := fun g => by funext k; by_cases h : k = j <;> simp [h]; subst h; rfl
       right_inv := fun p => by
        apply Prod.ext
        · simp
        · funext k; simp [k.2] }
     rw [← Equiv.sum_comp ePi.symm, sum_prod_type]
     have hsimp : ∀ u : HWI (bd.r j), ∀ rest : ((k : {k : Fin bd.t // k ≠ j}) → HWI (bd.r k.1)),
       (bd.r i : ℂ) * ((hwM (bd.r i) (ePi.symm (u, rest) i))ᴴ * M i).trace *
        hwM (bd.r j) (ePi.symm (u, rest) j) x y =
       (bd.r i : ℂ) * ((hwM (bd.r i) (rest ⟨i, hij⟩))ᴴ * M i).trace *
        hwM (bd.r j) u x y := fun u rest => by simp [ePi, hij]
     simp_rw [hsimp]
     rw [sum_comm]
     refine sum_eq_zero fun rest _ => ?_
     rw [← Finset.mul_sum, hwMat_first_moment (bd.hr j) x y, mul_zero]
    · intro h; exact absurd (mem_univ j) h
   · simp [bDA, hbd, Matrix.sum_apply, Matrix.smul_apply]
  · simp [bDA, hjk, Matrix.sum_apply, Matrix.smul_apply]
 calc
  a = bd.U * (bd.Uᴴ * a * bd.U) * bd.Uᴴ := by
     calc
      a = 1 * a * 1 := by simp
      _ = (bd.U * bd.Uᴴ) * a * (bd.U * bd.Uᴴ) := by rw [bd.U_mul_star]
      _ = bd.U * (bd.Uᴴ * a * bd.U) * bd.Uᴴ := by simp only [mma]
  _ = bd.U * (∑ g : BHW bd, coeff g • bDA bd.r bd.s (fun i => hwM (bd.r i) (g i))) * bd.Uᴴ := by
     rw [hM, hblock]
  _ = ∑ g : BHW bd, coeff g • bHW bd g := by
     simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, bHW]
lemma condExp_commutant_eq_avg {n : Type*} [Fintype n] [DecidableEq n]
  {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A) (X : Matrix n n ℂ) :
  cExp (comm A) X =
   ((Fintype.card (BHW bd) : ℂ)⁻¹) •
    ∑ g : BHW bd, bHW bd g * X * (bHW bd g)ᴴ := by
 have hN0 : (Fintype.card (BHW bd) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (ne_of_gt (blockHW_card_pos bd))
 let Y : Matrix n n ℂ :=
  ((Fintype.card (BHW bd) : ℂ)⁻¹) •
   ∑ g : BHW bd, bHW bd g * X * (bHW bd g)ᴴ
 have hY_mem : Y ∈ comm A := by
  rw [mem_commutant]
  intro a ha
  obtain ⟨coeff, rfl⟩ := blockHW_span_eq bd ha
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine sum_congr rfl fun g₀ _ => ?_
  rw [Matrix.mul_smul Y (coeff g₀) (bHW bd g₀),
   Matrix.smul_mul (coeff g₀) (bHW bd g₀) Y]
  congr 1
  have hU := bHW_u bd g₀
  have hsum_eq :
    ∑ g : BHW bd,
      bHW bd g₀ * (bHW bd g * X * (bHW bd g)ᴴ) * (bHW bd g₀)ᴴ =
    ∑ g : BHW bd, bHW bd g * X * (bHW bd g)ᴴ := by
   have hterm : ∀ g : BHW bd,
     bHW bd g₀ * (bHW bd g * X * (bHW bd g)ᴴ) * (bHW bd g₀)ᴴ =
      bHW bd (fun i => hwMul (bd.hr i) (g₀ i) (g i)) * X *
       (bHW bd (fun i => hwMul (bd.hr i) (g₀ i) (g i)))ᴴ := by
    intro g
    rw [← blockHWMat_mul bd g₀ g, ctM]
    simp only [mma]
   simp_rw [hterm]
   have hbij : Function.Bijective (fun g : BHW bd => fun i => hwMul (bd.hr i) (g₀ i) (g i)) := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun g₁ g₂ h => ?_, rfl⟩
    funext i
    exact (hwMul_bijective_left (bd.hr i) (g₀ i)).1 (congrFun h i)
   exact Fintype.sum_bijective _ hbij _ _ fun _ => rfl
  have hmul : bHW bd g₀ * Y * (bHW bd g₀)ᴴ = Y := by
   dsimp only [Y]
   rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, hsum_eq]
  calc
   Y * bHW bd g₀
    = (bHW bd g₀ * Y * (bHW bd g₀)ᴴ) * bHW bd g₀ := by rw [hmul]
   _ = bHW bd g₀ * Y * ((bHW bd g₀)ᴴ * bHW bd g₀) := by simp only [mma]
   _ = bHW bd g₀ * Y := by
      rw [← star_eq_conjTranspose, star_mul_self_of_mem hU, mm1]
 apply condExp_eq_of_mem_of_orthog (comm A) hY_mem
 intro c hc
 rw [ctS, sub_mul, trace_sub, sub_eq_zero]
 simp only [Y, conjTranspose_smul, conjTranspose_sum, Matrix.smul_mul, Matrix.sum_mul,
  trace_smul, trace_sum, smul_eq_mul]
 have hterm : ∀ g : BHW bd,
   ((bHW bd g * X * (bHW bd g)ᴴ)ᴴ * c).trace = (Xᴴ * c).trace := by
  intro g
  have hU := bHW_u bd g
  have hcomm : c * bHW bd g = bHW bd g * c := hc _ (blockHWMat_mem bd g)
  calc
   ((bHW bd g * X * (bHW bd g)ᴴ)ᴴ * c).trace
    = (bHW bd g * (Xᴴ * (bHW bd g)ᴴ * c)).trace := by
      simp only [ctM, ctct, mma]
   _ = (Xᴴ * (bHW bd g)ᴴ * c * bHW bd g).trace := by
      rw [trace_mul_comm]
   _ = (Xᴴ * ((bHW bd g)ᴴ * (c * bHW bd g))).trace := by
      simp only [mma]
   _ = (Xᴴ * (((bHW bd g)ᴴ * bHW bd g) * c)).trace := by
      rw [hcomm]; simp only [mma]
   _ = (Xᴴ * c).trace := by
      have hU' : (bHW bd g)ᴴ * bHW bd g = 1 := star_mul_self_of_mem hU
      rw [hU', m1m]
 simp_rw [hterm]
 rw [sum_const, card_univ, nsmul_eq_mul]
 have hconj : star ((Fintype.card (BHW bd) : ℂ)⁻¹) = (Fintype.card (BHW bd) : ℂ)⁻¹ := by
  simp
 rw [hconj, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
lemma opNorm_condExp_le {n : Type*} [Fintype n] [DecidableEq n]
  (A : StarSubalgebra ℂ (Matrix n n ℂ)) (X : Matrix n n ℂ) :
  ‖CLM (cExp A X)‖ ≤ ‖CLM X‖ := by
 obtain ⟨bd⟩ := exists_blockDecomp (comm A)
 have h1 := condExp_commutant_eq_avg bd X
 rw [bicommutant_eq A] at h1
 rw [h1]
 dsimp only [CLM]
 rw [map_smul, map_sum, norm_smul]
 have hpos : (0 : ℝ) < Fintype.card (BHW bd) := Nat.cast_pos.mpr (blockHW_card_pos bd)
 have hnorm_inv : ‖((Fintype.card (BHW bd) : ℂ)⁻¹)‖ = (Fintype.card (BHW bd) : ℝ)⁻¹ := by
  simp
 rw [hnorm_inv]
 calc
  (Fintype.card (BHW bd) : ℝ)⁻¹ *
    ‖∑ g : BHW bd, CLM (bHW bd g * X * (bHW bd g)ᴴ)‖
   ≤ (Fintype.card (BHW bd) : ℝ)⁻¹ *
    ∑ g : BHW bd, ‖CLM (bHW bd g * X * (bHW bd g)ᴴ)‖ := by
     gcongr
     exact norm_sum_le _ _
  _ ≤ (Fintype.card (BHW bd) : ℝ)⁻¹ *
    ∑ _g : BHW bd, ‖CLM X‖ := by
     gcongr with g _
     have hU : (bHW bd g)ᴴ ∈ unitaryGroup n ℂ :=
      Unitary.star_mem (bHW_u bd g)
     have heq : bHW bd g * X * (bHW bd g)ᴴ =
       ((bHW bd g)ᴴ)ᴴ * X * (bHW bd g)ᴴ := by simp
     rw [heq, opNorm_conj_unitary hU]
  _ = ‖CLM X‖ := by
     rw [sum_const, card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ (ne_of_gt hpos)]
/- Unitary polar rounding inside any StarSubalgebra -/
lemma exists_unitary_polar_square {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) :
  ∃ U : Matrix (Fin s) (Fin s) ℂ,
   U ∈ unitaryGroup (Fin s) ℂ ∧
   hsSq (U - M) ≤ hsSq (1 - Mᴴ * M) := by
 classical
 let S : Matrix (Fin s) (Fin s) ℂ := Mᴴ * M
 have hS : S.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
 have hS_nn : ∀ i, 0 ≤ hS.eigenvalues i := fun i =>
  Matrix.eigenvalues_conjTranspose_mul_self_nonneg M i
 let P : Matrix (Fin s) (Fin s) ℂ := hS.cfc sqrt
 let Spinv : Matrix (Fin s) (Fin s) ℂ := hS.cfc (fun t => if 0 < t then (sqrt t)⁻¹ else 0)
 let p : Matrix (Fin s) (Fin s) ℂ := hS.cfc (fun t => if 0 < t then 1 else 0)
 let W₀ : Matrix (Fin s) (Fin s) ℂ := M * Spinv
 have hSpinv_h : Spinvᴴ = Spinv := (cfc_isHermitian hS _).eq
 have hW₀_star_W₀ : W₀ᴴ * W₀ = p := by
  calc
   W₀ᴴ * W₀ = (Spinvᴴ * Mᴴ) * (M * Spinv) := by simp only [W₀, ctM]
   _ = Spinv * S * Spinv := by rw [hSpinv_h]; simp only [S, mma]
   _ = hS.cfc (fun t => if 0 < t then (sqrt t)⁻¹ else 0) * hS.cfc id *
      hS.cfc (fun t => if 0 < t then (sqrt t)⁻¹ else 0) := by rw [cfc_id hS]
   _ = p := by
     rw [cfc_mul, cfc_mul]
     refine cfc_congr hS fun i => ?_
     by_cases h : 0 < hS.eigenvalues i
     ·
      simp only [h, ↓reduceIte, id_eq]
      have hsq : sqrt (hS.eigenvalues i) ≠ 0 :=
       ne_of_gt (sqrt_pos.mpr h)
      field_simp [hsq]
      exact (sq_sqrt h.le).symm
     · simp [h]
 have hp_herm : pᴴ = p := (cfc_isHermitian hS _).eq
 have hp_idem : p * p = p := by
  rw [cfc_mul]
  refine cfc_congr hS fun i => by split_ifs <;> simp
 have hW₀_P : W₀ * P = M := by
  apply sub_eq_zero.mp
  rw [← hsSq_eq_zero_iff, hsSq_tr]
  have hmul : Spinv * P = p := by
   rw [cfc_mul]
   refine cfc_congr hS fun i => ?_
   by_cases h : 0 < hS.eigenvalues i
   · simp [h, inv_mul_cancel₀ (ne_of_gt (sqrt_pos.mpr h))]
   · simp [h]
  have hMp : W₀ * P - M = M * (p - 1) := by
   simp only [W₀, mma, hmul, mms, mm1]
  have hzero : (M * (p - 1))ᴴ * (M * (p - 1)) = 0 := by
   rw [ctM, ctS, conjTranspose_one, hp_herm]
   calc
    (p - 1) * Mᴴ * (M * (p - 1)) = (p - 1) * S * (p - 1) := by simp only [S, mma]
    _ = (p - hS.cfc (fun _ => 1)) * hS.cfc id * (p - hS.cfc (fun _ => 1)) := by
       rw [cfc_id hS, cfc_const hS 1, Complex.ofReal_one, one_smul]
    _ = hS.cfc (fun _ => 0) := by
       rw [cfc_sub, cfc_mul, cfc_mul]
       refine cfc_congr hS fun i => ?_
       have hnn := hS_nn i
       by_cases h : 0 < hS.eigenvalues i
       · simp [h]
       ·
        have h0 : hS.eigenvalues i = 0 := le_antisymm (not_lt.mp h) hnn
        simp [h0]
    _ = 0 := by rw [cfc_const hS 0]; simp
  rw [hMp, hzero, trace_zero, zero_re]
 have hW₀p : W₀ * p = W₀ := by
  dsimp only [W₀, Spinv, p]
  rw [mma, cfc_mul]
  congr 1
  refine cfc_congr hS fun i => by split_ifs <;> simp
 let q : Matrix (Fin s) (Fin s) ℂ := W₀ * W₀ᴴ
 have hq_herm : qᴴ = q := by simp only [q, ctM, ctct]
 have hq_idem : q * q = q := by
  calc
   (W₀ * W₀ᴴ) * (W₀ * W₀ᴴ) = W₀ * (W₀ᴴ * W₀) * W₀ᴴ := by simp only [mma]
   _ = W₀ * p * W₀ᴴ := by rw [hW₀_star_W₀]
   _ = W₀ * W₀ᴴ := by rw [hW₀p]
 -- Complete W₀ to a unitary U = W₀ + W₁ using ker(p) and ker(q)
 let Kp : Submodule ℂ (EuclideanSpace ℂ (Fin s)) := LinearMap.ker (CLM p).toLinearMap
 let Kq : Submodule ℂ (EuclideanSpace ℂ (Fin s)) := LinearMap.ker (CLM q).toLinearMap
 have hrank_eq : Module.finrank ℂ Kp = Module.finrank ℂ Kq := by
  have htr : p.trace = q.trace := by
   rw [← hW₀_star_W₀, trace_mul_comm]
  have htr_proj : ∀ (Q : Matrix (Fin s) (Fin s) ℂ), Q.IsHermitian → Q * Q = Q →
    (Q.trace).re + Module.finrank ℂ (LinearMap.ker (CLM Q).toLinearMap) = s := by
   intro Q hQh hQi
   have hQe : ∀ i, hQh.eigenvalues i = 0 ∨ hQh.eigenvalues i = 1 := by
    intro i
    have hid : hQh.cfc (fun t => t) = Q := cfc_id hQh
    have hsq : hQh.cfc (fun t => t * t) = hQh.cfc (fun t => t) := by
     rw [← cfc_mul, hid, hQi]
    have hev : (hQh.cfc (fun t => t * t) - hQh.cfc (fun t => t)) = 0 := sub_eq_zero.mpr hsq
    have h0 := hsSq_cfc hQh (fun t => t * t - t)
    rw [← cfc_sub, hev, show hsSq (0 : Matrix (Fin s) (Fin s) ℂ) = 0 by simp [hsSq]] at h0
    have hi : (hQh.eigenvalues i * hQh.eigenvalues i - hQh.eigenvalues i) ^ 2 = 0 :=
     (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h0.symm i (mem_univ i)
    have h1 : hQh.eigenvalues i * (hQh.eigenvalues i - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
   have htrQ : (Q.trace).re = (univ.filter fun i => hQh.eigenvalues i ≠ 0).card := by
    have htr_id : Q.trace = ∑ i, ((hQh.eigenvalues i : ℝ) : ℂ) := by
     conv_lhs => rw [← cfc_id hQh]
     rw [trace_cfc]
     rfl
    rw [htr_id, re_sum]
    simp only [Complex.ofReal_re]
    rw [← sum_filter_add_sum_filter_not univ (fun i => hQh.eigenvalues i ≠ 0)]
    have h1 : ∑ i ∈ univ.filter (fun i => hQh.eigenvalues i ≠ 0), hQh.eigenvalues i =
      (univ.filter fun i => hQh.eigenvalues i ≠ 0).card := by
     have : ∀ i ∈ univ.filter (fun i => hQh.eigenvalues i ≠ 0), hQh.eigenvalues i = 1 := by
      intro i hi
      rcases hQe i with h0 | h1
      · exact absurd h0 (mem_filter.mp hi).2
      · exact h1
     rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_one]
    have h2 : ∑ i ∈ univ.filter (fun i => ¬ hQh.eigenvalues i ≠ 0), hQh.eigenvalues i = 0 := by
     refine sum_eq_zero fun i hi => ?_
     simpa using (mem_filter.mp hi).2
    rw [h1, h2, add_zero]
   have hkerQ : Module.finrank ℂ (LinearMap.ker (CLM Q).toLinearMap) =
     (univ.filter fun i => hQh.eigenvalues i = 0).card := by
    let Z := univ.filter fun i => hQh.eigenvalues i = 0
    have hker_eq : LinearMap.ker (CLM Q).toLinearMap =
      Submodule.span ℂ (Set.range fun i : {i // i ∈ Z} => hQh.eigenvectorBasis i.1) := by
     apply le_antisymm
     ·
      intro v hv
      rw [LinearMap.mem_ker] at hv
      have hrepr := (hQh.eigenvectorBasis.sum_repr' v).symm
      have hcoeff0 : ∀ i : Fin s, hQh.eigenvalues i ≠ 0 → ⟪hQh.eigenvectorBasis i, v⟫_ℂ = 0 := by
       intro i hne
       have hact : CLM Q (hQh.eigenvectorBasis i) =
         (hQh.eigenvalues i : ℂ) • hQh.eigenvectorBasis i := by
        apply WithLp.ofLp_injective
        simpa [ofLp_toEuclideanCLM, RCLike.real_smul_eq_coe_smul] using
         hQh.mulVec_eigenvectorBasis i
       have h0 : ⟪CLM Q (hQh.eigenvectorBasis i), v⟫_ℂ = 0 := by
        have hsymm : CLM Q = ContinuousLinearMap.adjoint (CLM Q) := by
         rw [toCLM_adjoint, hQh.eq]
        conv_lhs => rw [hsymm]
        rw [ContinuousLinearMap.adjoint_inner_left]
        change ⟪hQh.eigenvectorBasis i, (CLM Q).toLinearMap v⟫_ℂ = 0
        rw [hv, inner_zero_right]
       rw [hact, inner_smul_left] at h0
       have hcne : (starRingEnd ℂ) (hQh.eigenvalues i : ℂ) ≠ 0 := by
        simpa using hne
       exact (mul_eq_zero.mp h0).resolve_left hcne
      rw [hrepr, ← sum_filter_add_sum_filter_not univ (fun i => hQh.eigenvalues i = 0)]
      have hrest : ∑ i ∈ univ.filter (fun i => ¬ hQh.eigenvalues i = 0),
        ⟪hQh.eigenvectorBasis i, v⟫_ℂ • hQh.eigenvectorBasis i = 0 :=
       sum_eq_zero fun i hi => by rw [hcoeff0 i (mem_filter.mp hi).2, zero_smul]
      rw [hrest, add_zero]
      exact Submodule.sum_mem _ fun i hi =>
       Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
     ·
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨⟨i, hi⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      change CLM Q (hQh.eigenvectorBasis i) = 0
      apply WithLp.ofLp_injective
      rw [ofLp_toEuclideanCLM, hQh.mulVec_eigenvectorBasis i,
       (mem_filter.mp hi).2, zero_smul]
      rfl
    rw [hker_eq]
    have hli : LinearIndependent ℂ (fun i : {i // i ∈ Z} => hQh.eigenvectorBasis i.1) :=
     hQh.eigenvectorBasis.toBasis.linearIndependent.comp _ Subtype.val_injective
    rw [finrank_span_eq_card hli, Fintype.card_coe]
   rw [htrQ, hkerQ]
   have hsum := Finset.card_filter_add_card_filter_not (s := univ) (p := fun i : Fin s => hQh.eigenvalues i = 0)
   rw [card_univ, card_fin] at hsum
   have heq' : (univ.filter fun i : Fin s => ¬ hQh.eigenvalues i = 0) =
     (univ.filter fun i : Fin s => hQh.eigenvalues i ≠ 0) := rfl
   rw [heq'] at hsum
   exact_mod_cast (by omega : (univ.filter fun i : Fin s => hQh.eigenvalues i ≠ 0).card +
    (univ.filter fun i : Fin s => hQh.eigenvalues i = 0).card = s)
  have h1 := htr_proj p hp_herm hp_idem
  have h2 := htr_proj q hq_herm hq_idem
  rw [htr] at h1
  have hcast : ((Module.finrank ℂ Kp : ℝ)) = ((Module.finrank ℂ Kq : ℝ)) := by linarith
  exact_mod_cast hcast
 let bp : OrthonormalBasis (Fin (Module.finrank ℂ Kp)) ℂ Kp := stdOrthonormalBasis ℂ Kp
 let bq : OrthonormalBasis (Fin (Module.finrank ℂ Kp)) ℂ Kq :=
  (stdOrthonormalBasis ℂ Kq).reindex (Fin.castOrderIso hrank_eq.symm).toEquiv
 let W₁ : Matrix (Fin s) (Fin s) ℂ :=
  fun x y => ∑ k : Fin (Module.finrank ℂ Kp), (bq k).1.ofLp x * star ((bp k).1.ofLp y)
 have hactW₁ : ∀ w : EuclideanSpace ℂ (Fin s),
   CLM W₁ w = ∑ k, ⟪(bp k).1, w⟫_ℂ • (bq k).1 := by
  intro w
  apply WithLp.ofLp_injective; ext x
  dsimp only [CLM]
  rw [ofLp_toEuclideanCLM, mulVec, dotProduct]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  dsimp only [W₁]
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [inner_eq_star_dotProduct, dotProduct, Finset.sum_mul]
  refine sum_congr rfl fun y _ => by simp only [Pi.star_apply]; ring
 have hW₁_star_W₁ : W₁ᴴ * W₁ = 1 - p := by
  have h1 : ∀ v : EuclideanSpace ℂ (Fin s),
    CLM (W₁ᴴ * W₁) v = CLM (1 - p) v := by
   intro v
   have hactS : ∀ w : EuclideanSpace ℂ (Fin s),
     CLM W₁ᴴ w = ∑ k, ⟪(bq k).1, w⟫_ℂ • (bp k).1 := by
    intro w
    apply WithLp.ofLp_injective; ext y
    dsimp only [CLM]
    rw [ofLp_toEuclideanCLM, mulVec, dotProduct]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    have hterm : ∀ x, W₁ᴴ y x * w.ofLp x =
      ∑ k, star ((bq k).1.ofLp x) * (bp k).1.ofLp y * w.ofLp x := by
     intro x
     rw [ctA]
     dsimp only [W₁]
     rw [star_sum, Finset.sum_mul]
     refine sum_congr rfl fun k _ => ?_
     rw [star_mul, star_star, mul_comm (star ((bq k).1.ofLp x))]
    simp_rw [hterm]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [inner_eq_star_dotProduct, dotProduct, Finset.sum_mul]
    refine sum_congr rfl fun x _ => by simp only [Pi.star_apply]; ring
   have hmul_act : CLM (W₁ᴴ * W₁) v = CLM W₁ᴴ (CLM W₁ v) := by
    dsimp only [CLM]; rw [map_mul]; rfl
   rw [hmul_act, hactW₁, hactS]
   simp only [inner_sum, inner_smul_right]
   have horth : ∀ k l, ⟪(bq k).1, (bq l).1⟫_ℂ = if k = l then 1 else 0 := by
    intro k l
    exact (orthonormal_iff_ite.mp bq.orthonormal) k l
   simp only [horth, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
   have hproj : ∑ k, ⟪(bp k).1, v⟫_ℂ • (bp k).1 = Kp.starProjection v := by
    have hmem : ∑ k, ⟪(bp k).1, v⟫_ℂ • (bp k).1 ∈ Kp :=
     Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (bp k).2
    have hdiff : v - ∑ k, ⟪(bp k).1, v⟫_ℂ • (bp k).1 ∈ Kpᗮ := by
     rw [Submodule.mem_orthogonal]
     intro u hu
     let u' : Kp := ⟨u, hu⟩
     have hu' : u = ∑ k, ⟪bp k, u'⟫_ℂ • (bp k).1 := by
      have := congrArg Subtype.val (bp.sum_repr' u').symm
      simpa [u'] using this
     rw [hu', sum_inner]
     refine sum_eq_zero fun k _ => ?_
     rw [inner_smul_left, inner_sub_right, inner_sum]
     have horthp : ∀ l, ⟪(bp k).1, (bp l).1⟫_ℂ = if k = l then 1 else 0 :=
      fun l => (orthonormal_iff_ite.mp bp.orthonormal) k l
     simp only [inner_smul_right, horthp, mul_ite, mul_one, mul_zero, sum_ite_eq,
      mem_univ, ↓reduceIte, sub_self, mul_zero]
    have h1' := Kp.starProjection_eq_self_iff.mpr hmem
    have h2' := starProjection_eq_zero_of_mem_orthogonal Kp hdiff
    have hsum : v = (∑ k, ⟪(bp k).1, v⟫_ℂ • (bp k).1) + (v - ∑ k, ⟪(bp k).1, v⟫_ℂ • (bp k).1) := by abel
    conv_rhs => rw [hsum, map_add, h1', h2', add_zero]
   rw [hproj]
   have h1p : CLM (1 - p) v ∈ Kp := by
    rw [LinearMap.mem_ker]
    change CLM p (CLM (1 - p) v) = 0
    have hcomp : CLM p (CLM (1 - p) v) = CLM (p * (1 - p)) v := by
     dsimp only [CLM]; rw [map_mul]; rfl
    rw [hcomp, mms, mm1, hp_idem, sub_self]
    dsimp only [CLM]; rw [map_zero]; rfl
   have hpv : CLM p v ∈ Kpᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have hsymm : CLM p = ContinuousLinearMap.adjoint (CLM p) := by
     rw [toCLM_adjoint, hp_herm]
    conv_lhs => rw [hsymm]
    rw [ContinuousLinearMap.adjoint_inner_right]
    change ⟪(CLM p).toLinearMap u, v⟫_ℂ = 0
    rw [hu, inner_zero_left]
   have hv_split : v = CLM (1 - p) v + CLM p v := by
    dsimp only [CLM]
    rw [map_sub, map_one]
    exact (sub_add_cancel v _).symm
   conv_lhs => rw [hv_split, map_add, Kp.starProjection_eq_self_iff.mpr h1p,
    starProjection_eq_zero_of_mem_orthogonal Kp hpv, add_zero]
  exact (toEuclideanCLM (n := Fin s) (𝕜 := ℂ)).injective (ContinuousLinearMap.ext h1)
 have hW₀_star_W₁ : W₀ᴴ * W₁ = 0 := by
  have h1 : W₀ᴴ * W₁ = W₀ᴴ * q * W₁ := by
   have : W₀ᴴ * q = W₀ᴴ := by
    calc
     W₀ᴴ * (W₀ * W₀ᴴ) = (W₀ᴴ * W₀) * W₀ᴴ := by simp only [mma]
     _ = p * W₀ᴴ := by rw [hW₀_star_W₀]
     _ = (W₀ * p)ᴴ := by rw [ctM W₀ p, hp_herm]
     _ = W₀ᴴ := by rw [hW₀p]
   rw [this]
  have hqW₁ : q * W₁ = 0 := by
   apply (toEuclideanCLM (n := Fin s) (𝕜 := ℂ)).injective
   apply ContinuousLinearMap.ext
   intro v
   rw [map_mul, map_zero]
   change CLM q (CLM W₁ v) = 0
   have hW₁v : CLM W₁ v ∈ Kq := by
    rw [hactW₁]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (bq k).2
   exact LinearMap.mem_ker.mp hW₁v
  rw [h1, mma, hqW₁, Matrix.mul_zero]
 have hW₁_star_W₀ : W₁ᴴ * W₀ = 0 := by
  have := congrArg Matrix.conjTranspose hW₀_star_W₁
  simpa [ctM] using this
 let U : Matrix (Fin s) (Fin s) ℂ := W₀ + W₁
 have hU_unit : U ∈ unitaryGroup (Fin s) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  simp only [U, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, hW₀_star_W₀,
   hW₀_star_W₁, hW₁_star_W₀, hW₁_star_W₁]
  abel
 have hW₁_P : W₁ * P = 0 := by
  have hpP : p * P = P := by
   rw [cfc_mul]
   refine cfc_congr hS fun i => ?_
   have hnn := hS_nn i
   by_cases h : 0 < hS.eigenvalues i
   · simp [h]
   ·
    have h0 : hS.eigenvalues i = 0 := le_antisymm (not_lt.mp h) hnn
    simp [h0]
  have hW₁p : W₁ * p = 0 := by
   apply (hsSq_eq_zero_iff _).mp
   rw [hsSq_tr, ctM, hp_herm, mma,
    ← mma W₁ᴴ, hW₁_star_W₁, msm, m1m, hp_idem,
    sub_self, Matrix.mul_zero, trace_zero, zero_re]
  rw [← hpP, ← mma, hW₁p, Matrix.zero_mul]
 have hUP : U * P = M := by
  simp only [U, Matrix.add_mul, hW₀_P, hW₁_P, add_zero]
 refine ⟨U, hU_unit, ?_⟩
 have hdiff : U - M = U * (1 - P) := by rw [mms, mm1, hUP]
 rw [hdiff, hsSq_isoL U (star_mul_self_of_mem hU_unit)]
 have h1P : 1 - P = hS.cfc (fun t => 1 - sqrt t) := by
  dsimp only [P]
  rw [← cfc_sub, cfc_const hS 1]; simp
 have h1S : 1 - Mᴴ * M = hS.cfc (fun t => 1 - t) := by
  change 1 - S = _
  have hid : hS.cfc (fun t => t) = S := cfc_id hS
  rw [← cfc_sub, cfc_const hS 1, hid]; simp
 rw [h1P, h1S, hsSq_cfc, hsSq_cfc]
 refine sum_le_sum fun i _ => ?_
 have hnn := hS_nn i
 have hsq : (1 - hS.eigenvalues i) ^ 2 = (1 - sqrt (hS.eigenvalues i)) ^ 2 *
   (1 + sqrt (hS.eigenvalues i)) ^ 2 := by
  rw [← mul_pow]
  congr 1
  nlinarith [sq_sqrt hnn]
 rw [hsq]
 have hge1 : 1 ≤ (1 + sqrt (hS.eigenvalues i)) ^ 2 := by
  nlinarith [sqrt_nonneg (hS.eigenvalues i)]
 nlinarith [sq_nonneg (1 - sqrt (hS.eigenvalues i))]
lemma exists_unitary_polar_in_subalgebra {n : Type*} [Fintype n] [DecidableEq n]
  (A : StarSubalgebra ℂ (Matrix n n ℂ)) {M : Matrix n n ℂ} (hM : M ∈ A) :
  ∃ U : Matrix n n ℂ, U ∈ A ∧ U ∈ unitaryGroup n ℂ ∧
   hsSq (U - M) ≤ hsSq (1 - Mᴴ * M) := by
 obtain ⟨bd⟩ := exists_blockDecomp A
 obtain ⟨Mblk, hMblk⟩ := (bd.mem_iff M).mp hM
 have hUblk : ∀ i : Fin bd.t, ∃ U_i : Matrix (Fin (bd.r i)) (Fin (bd.r i)) ℂ,
   U_i ∈ unitaryGroup (Fin (bd.r i)) ℂ ∧
   hsSq (U_i - Mblk i) ≤ hsSq (1 - (Mblk i)ᴴ * Mblk i) :=
  fun i => exists_unitary_polar_square (Mblk i)
 let Ublk : (i : Fin bd.t) → Matrix (Fin (bd.r i)) (Fin (bd.r i)) ℂ := fun i => (hUblk i).choose
 let U : Matrix n n ℂ := bd.U * bDA bd.r bd.s Ublk * bd.Uᴴ
 have hU_mem : U ∈ A := by
  rw [bd.mem_iff]
  refine ⟨Ublk, ?_⟩
  simp only [U]
  calc
   bd.Uᴴ * (bd.U * bDA bd.r bd.s Ublk * bd.Uᴴ) * bd.U
    = (bd.Uᴴ * bd.U) * bDA bd.r bd.s Ublk * (bd.Uᴴ * bd.U) := by simp [mma]
   _ = bDA bd.r bd.s Ublk := by rw [bd.U_star_mul, m1m, mm1]
 have hU_unit : U ∈ unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  simp only [U, ctM, ctct,
   blockDiagA_conjTranspose]
  have h1 : (fun i : Fin bd.t => (Ublk i)ᴴ * Ublk i) = fun _ => 1 :=
   funext fun i => star_mul_self_of_mem (hUblk i).choose_spec.1
  calc
   bd.U * (bDA bd.r bd.s (fun i => (Ublk i)ᴴ) * bd.Uᴴ) *
    (bd.U * bDA bd.r bd.s Ublk * bd.Uᴴ)
    = bd.U * (bDA bd.r bd.s (fun i => (Ublk i)ᴴ) *
      ((bd.Uᴴ * bd.U) * bDA bd.r bd.s Ublk)) * bd.Uᴴ := by simp only [mma]
   _ = bd.U * bDA bd.r bd.s (fun i => (Ublk i)ᴴ * Ublk i) * bd.Uᴴ := by
      rw [bd.U_star_mul, m1m, blockDiagA_mul]
   _ = bd.U * bDA bd.r bd.s (fun _ => 1) * bd.Uᴴ := by rw [h1]
   _ = 1 := by rw [blockDiagA_one, mm1, bd.U_mul_star]
 have hhsSq_block : ∀ F : (i : Fin bd.t) → Matrix (Fin (bd.r i)) (Fin (bd.r i)) ℂ,
   hsSq (bDA bd.r bd.s F) = ∑ i : Fin bd.t, (bd.s i : ℝ) * hsSq (F i) := by
  intro F
  unfold hsSq bDA
  rw [Fintype.sum_sigma]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_prod_type]
  have hinner : ∀ (a : Fin (bd.r i)) (b : Fin (bd.s i)),
    (∑ p : (Σ j : Fin bd.t, Fin (bd.r j) × Fin (bd.s j)),
     ‖if h : i = p.1 then if b = h ▸ p.2.2 then F i a (h ▸ p.2.1) else 0 else 0‖ ^ 2) =
    ∑ c : Fin (bd.r i), ‖F i a c‖ ^ 2 := by
   intro a b
   rw [Fintype.sum_sigma, sum_eq_single i]
   ·
    simp only [↓reduceDIte, sum_prod_type]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_eq_single b]
    · simp
    · intro d _ hdb; simp [hdb.symm]
    · intro h; exact absurd (mem_univ b) h
   · intro j _ hji; exact sum_eq_zero fun p _ => by simp [Ne.symm hji]
   · intro h; exact absurd (mem_univ i) h
  simp_rw [hinner]
  simp [sum_const, nsmul_eq_mul, Finset.mul_sum, mul_comm]
 refine ⟨U, hU_mem, hU_unit, ?_⟩
 have hL : hsSq (U - M) = hsSq (bDA bd.r bd.s (fun i => Ublk i - Mblk i)) := by
  rw [← hsSq_isoL bd.Uᴴ (by simpa using bd.U_mul_star),
   ← hsSq_coisoR bd.U bd.U_mul_star]
  have heq : bd.Uᴴ * (U - M) * bd.U = bDA bd.r bd.s (fun i => Ublk i - Mblk i) := by
   rw [mms, msm, hMblk]
   have hU' : bd.Uᴴ * U * bd.U = bDA bd.r bd.s Ublk := by
    simp only [U]
    calc
     bd.Uᴴ * (bd.U * bDA bd.r bd.s Ublk * bd.Uᴴ) * bd.U
      = (bd.Uᴴ * bd.U) * bDA bd.r bd.s Ublk * (bd.Uᴴ * bd.U) := by simp only [mma]
     _ = bDA bd.r bd.s Ublk := by rw [bd.U_star_mul, m1m, mm1]
   rw [hU']
   ext ⟨i, a, b⟩ ⟨j, c, d⟩
   by_cases hij : i = j
   ·
    subst hij
    by_cases hbd : b = d
    · subst hbd; simp [bDA]
    · simp [bDA, hbd]
   · simp [bDA, hij]
  rw [heq]
 have hR : hsSq (1 - Mᴴ * M) = hsSq (bDA bd.r bd.s (fun i => 1 - (Mblk i)ᴴ * Mblk i)) := by
  rw [← hsSq_isoL bd.Uᴴ (by simpa using bd.U_mul_star),
   ← hsSq_coisoR bd.U bd.U_mul_star]
  have heq : bd.Uᴴ * (1 - Mᴴ * M) * bd.U = bDA bd.r bd.s (fun i => 1 - (Mblk i)ᴴ * Mblk i) := by
   have hM' : bd.Uᴴ * Mᴴ * bd.U = bDA bd.r bd.s (fun i => (Mblk i)ᴴ) := by
    have := congrArg Matrix.conjTranspose hMblk
    rw [ctM, ctM, ctct,
     blockDiagA_conjTranspose] at this
    simpa [mma] using this
   have hMM : bd.Uᴴ * (Mᴴ * M) * bd.U = bDA bd.r bd.s (fun i => (Mblk i)ᴴ * Mblk i) := by
    calc
     bd.Uᴴ * (Mᴴ * M) * bd.U
      = bd.Uᴴ * Mᴴ * (bd.U * bd.Uᴴ) * M * bd.U := by
        rw [bd.U_mul_star, mm1]; simp only [mma]
     _ = (bd.Uᴴ * Mᴴ * bd.U) * (bd.Uᴴ * M * bd.U) := by simp only [mma]
     _ = bDA bd.r bd.s (fun i => (Mblk i)ᴴ * Mblk i) := by
        rw [hM', hMblk, blockDiagA_mul]
   rw [mms, msm, mm1, bd.U_star_mul, hMM, ← blockDiagA_one bd.r bd.s]
   ext ⟨i, a, b⟩ ⟨j, c, d⟩
   by_cases hij : i = j
   ·
    subst hij
    by_cases hbd : b = d
    · subst hbd; simp [bDA]
    · simp [bDA, hbd]
   · simp [bDA, hij]
  rw [heq]
 rw [hL, hR, hhsSq_block, hhsSq_block]
 refine sum_le_sum fun i _ => ?_
 gcongr
 exact (hUblk i).choose_spec.2
end OneDesign
/- ### 6a. Block matrix units, central projections, projection ranks, and homomorphic block decompositions -/
section BlockMatrixUnits
lemma hsSq_isometry_mul_le {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n]
  (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (X : Matrix m k ℂ) :
  hsSq (Vᴴ * X) ≤ hsSq X := by
 have hQ : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
  calc
   (V * Vᴴ) * (V * Vᴴ) = V * ((Vᴴ * V) * Vᴴ) := by simp only [mma]
   _ = V * Vᴴ := by rw [hV, m1m]
 have h1 : hsSq (Vᴴ * X) = hsSq ((V * Vᴴ) * X) := by
  rw [← hsSq_isoL V hV (Vᴴ * X), mma]
 rw [h1]
 exact hsSq_proj_mul_le (V * Vᴴ) (by simp) hQ X
lemma opN_conjPI {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]
  (W : Matrix m n ℂ) (hsrc : (Wᴴ * W) * (Wᴴ * W) = Wᴴ * W)
  (X : Matrix n n ℂ) :
  ‖CLM (W * X * Wᴴ)‖ ≤ ‖CLM X‖ := by
 have hPh : (Wᴴ * W)ᴴ = Wᴴ * W := by simp
 have hWnorm : ∀ v : EuclideanSpace ℂ n, ‖WithLp.toLp 2 (W.mulVec v.ofLp)‖ ≤ ‖v‖ := by
  intro v
  have hsq : ‖WithLp.toLp 2 (W.mulVec v.ofLp)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
   have h1 : ((‖WithLp.toLp 2 (W.mulVec v.ofLp)‖ ^ 2 : ℝ) : ℂ) =
     ⟪v, CLM (Wᴴ * W) v⟫_ℂ := by
    have hself : ((‖WithLp.toLp 2 (W.mulVec v.ofLp)‖ ^ 2 : ℝ) : ℂ) =
      ⟪WithLp.toLp 2 (W.mulVec v.ofLp), WithLp.toLp 2 (W.mulVec v.ofLp)⟫_ℂ := by
     rw [inner_self_eq_norm_sq_to_K]; simp
    rw [hself]
    change ∑ i : m, (W.mulVec v.ofLp i) * star (W.mulVec v.ofLp i) =
     ∑ j : n, (CLM (Wᴴ * W) v).ofLp j * star (v.ofLp j)
    simp only [ofLp_toEuclideanCLM, mulVec, dotProduct, mul_apply,
     Finset.sum_mul, Finset.mul_sum, star_sum, star_mul, ctA]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    refine sum_congr rfl fun k _ => by ring
   have h2 : ⟪v, CLM (Wᴴ * W) v⟫_ℂ = ⟪CLM (Wᴴ * W) v, CLM (Wᴴ * W) v⟫_ℂ := by
    have hcomp : CLM (Wᴴ * W) v = CLM (Wᴴ * W) (CLM (Wᴴ * W) v) := by
     have : CLM ((Wᴴ * W) * (Wᴴ * W)) v = CLM (Wᴴ * W) (CLM (Wᴴ * W) v) := by
      dsimp only [CLM]; rw [map_mul]; rfl
     rw [← this, hsrc]
    calc
     ⟪v, CLM (Wᴴ * W) v⟫_ℂ
      = ⟪v, ContinuousLinearMap.adjoint (CLM (Wᴴ * W)) (CLM (Wᴴ * W) v)⟫_ℂ := by
        rw [toCLM_adjoint, hPh, ← hcomp]
     _ = ⟪CLM (Wᴴ * W) v, CLM (Wᴴ * W) v⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_right _ _ _
   have h3 : ((‖CLM (Wᴴ * W) v‖ ^ 2 : ℝ) : ℂ) = ⟪CLM (Wᴴ * W) v, CLM (Wᴴ * W) v⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]; simp
   have hnorm_eq : ‖WithLp.toLp 2 (W.mulVec v.ofLp)‖ ^ 2 = ‖CLM (Wᴴ * W) v‖ ^ 2 := by
    exact_mod_cast (h1.trans h2).trans h3.symm
   rw [hnorm_eq]
   have hsub : ‖v‖ ^ 2 - ‖CLM (Wᴴ * W) v‖ ^ 2 = ‖v - CLM (Wᴴ * W) v‖ ^ 2 := by
    have hC : ((‖v‖ ^ 2 - ‖CLM (Wᴴ * W) v‖ ^ 2 : ℝ) : ℂ) =
      ((‖v - CLM (Wᴴ * W) v‖ ^ 2 : ℝ) : ℂ) := by
     have hv1 : ((‖v‖ ^ 2 : ℝ) : ℂ) = ⟪v, v⟫_ℂ := by rw [inner_self_eq_norm_sq_to_K]; simp
     have hv2 : ((‖v - CLM (Wᴴ * W) v‖ ^ 2 : ℝ) : ℂ) =
       ⟪v - CLM (Wᴴ * W) v, v - CLM (Wᴴ * W) v⟫_ℂ := by
      rw [inner_self_eq_norm_sq_to_K]; simp
     rw [ofReal_sub, hv1, h3, hv2, inner_sub_left, inner_sub_right, inner_sub_right]
     have hsym : ⟪CLM (Wᴴ * W) v, v⟫_ℂ = ⟪CLM (Wᴴ * W) v, CLM (Wᴴ * W) v⟫_ℂ := by
      have := congrArg (starRingEnd ℂ) h2
      rw [inner_conj_symm, inner_conj_symm] at this
      exact this
     rw [h2, hsym]
     ring
    exact_mod_cast hC
   linarith [sq_nonneg ‖v - CLM (Wᴴ * W) v‖]
  nlinarith [norm_nonneg (WithLp.toLp 2 (W.mulVec v.ofLp)), norm_nonneg v]
 have hWhnorm : ∀ u : EuclideanSpace ℂ m, ‖WithLp.toLp 2 (Wᴴ.mulVec u.ofLp)‖ ≤ ‖u‖ := by
  intro u
  have hsq : ‖WithLp.toLp 2 (Wᴴ.mulVec u.ofLp)‖ ^ 2 ≤ ‖u‖ * ‖WithLp.toLp 2 (Wᴴ.mulVec u.ofLp)‖ := by
   have h1 : ((‖WithLp.toLp 2 (Wᴴ.mulVec u.ofLp)‖ ^ 2 : ℝ) : ℂ) =
     ⟪u, WithLp.toLp 2 (W.mulVec (Wᴴ.mulVec u.ofLp))⟫_ℂ := by
    have hself : ((‖WithLp.toLp 2 (Wᴴ.mulVec u.ofLp)‖ ^ 2 : ℝ) : ℂ) =
      ⟪WithLp.toLp 2 (Wᴴ.mulVec u.ofLp), WithLp.toLp 2 (Wᴴ.mulVec u.ofLp)⟫_ℂ := by
     rw [inner_self_eq_norm_sq_to_K]; simp
    rw [hself]
    change ∑ j : n, (Wᴴ.mulVec u.ofLp j) * star (Wᴴ.mulVec u.ofLp j) =
     ∑ i : m, (W.mulVec (Wᴴ.mulVec u.ofLp) i) * star (u.ofLp i)
    simp only [mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, star_sum, star_mul,
     ctA, star_star]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ =>
     sum_congr rfl fun k _ => by ring
   have hcs := @norm_inner_le_norm ℂ (EuclideanSpace ℂ m) _ _ _ u
    (WithLp.toLp 2 (W.mulVec (WithLp.toLp 2 (Wᴴ.mulVec u.ofLp)).ofLp))
   have hnorm1 : ‖((‖WithLp.toLp 2 (Wᴴ.mulVec u.ofLp)‖ ^ 2 : ℝ) : ℂ)‖ =
     ‖WithLp.toLp 2 (Wᴴ.mulVec u.ofLp)‖ ^ 2 := by
    rw [norm_real, Real.norm_of_nonneg (sq_nonneg _)]
   rw [← hnorm1, h1]
   exact hcs.trans (mul_le_mul_of_nonneg_left (hWnorm _) (norm_nonneg u))
  nlinarith [norm_nonneg (WithLp.toLp 2 (Wᴴ.mulVec u.ofLp)), norm_nonneg u]
 refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (CLM X)) fun u => ?_
 have heq : CLM (W * X * Wᴴ) u =
   WithLp.toLp 2 (W.mulVec (CLM X (WithLp.toLp 2 (Wᴴ.mulVec u.ofLp))).ofLp) := by
  apply WithLp.ofLp_injective
  dsimp only [CLM]
  rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, Matrix.mulVec_mulVec,
   Matrix.mulVec_mulVec]
 rw [heq]
 calc
  ‖WithLp.toLp 2 (W.mulVec (CLM X (WithLp.toLp 2 (Wᴴ.mulVec u.ofLp))).ofLp)‖
   ≤ ‖CLM X (WithLp.toLp 2 (Wᴴ.mulVec u.ofLp))‖ := hWnorm _
  _ ≤ ‖CLM X‖ * ‖WithLp.toLp 2 (Wᴴ.mulVec u.ofLp)‖ := (CLM X).le_opNorm _
  _ ≤ ‖CLM X‖ * ‖u‖ := mul_le_mul_of_nonneg_left (hWhnorm u) (norm_nonneg _)
lemma opNorm_blockDiagA_le {t : ℕ} {r s : Fin t → ℕ}
  (M : (i : Fin t) → Matrix (Fin (r i)) (Fin (r i)) ℂ) {C : ℝ} (hC : 0 ≤ C)
  (hM : ∀ i, ‖CLM (M i)‖ ≤ C) :
  ‖CLM (bDA r s M)‖ ≤ C := by
 refine ContinuousLinearMap.opNorm_le_bound _ hC fun v => ?_
 have hsq : ‖CLM (bDA r s M) v‖ ^ 2 ≤ (C * ‖v‖) ^ 2 := by
  rw [mul_pow, norm_sq_eq, norm_sq_eq, Fintype.sum_sigma,
   Fintype.sum_sigma, Finset.mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [sum_prod_type, sum_prod_type, sum_comm,
   sum_comm (f := fun a b => ‖v.ofLp ⟨i, a, b⟩‖ ^ 2), Finset.mul_sum]
  refine sum_le_sum fun b _ => ?_
  let w : EuclideanSpace ℂ (Fin (r i)) := WithLp.toLp 2 fun a => v.ofLp ⟨i, a, b⟩
  have hact : ∀ a : Fin (r i), (CLM (bDA r s M) v).ofLp ⟨i, a, b⟩ =
    (CLM (M i) w).ofLp a := by
   intro a
   dsimp only [CLM]
   rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, mulVec, mulVec,
    dotProduct, dotProduct, Fintype.sum_sigma, sum_eq_single i]
   ·
    simp only [bDA, ↓reduceDIte, sum_prod_type]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_eq_single b]
    · simp [w]
    · intro d _ hdb; simp [hdb.symm]
    · intro h; exact absurd (mem_univ b) h
   · intro j _ hji; exact sum_eq_zero fun p _ => by simp [bDA, Ne.symm hji]
   · intro h; exact absurd (mem_univ i) h
  simp_rw [hact]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) ((CLM (M i)).le_opNorm w) 2
  rw [mul_pow, norm_sq_eq, norm_sq_eq] at h1
  refine h1.trans ?_
  gcongr
  exact hM i
 nlinarith [norm_nonneg (CLM (bDA r s M) v), mul_nonneg hC (norm_nonneg v)]
lemma opNorm_le_blockDiagA {t : ℕ} {r s : Fin t → ℕ} (hs : ∀ i, 0 < s i)
  (M : (i : Fin t) → Matrix (Fin (r i)) (Fin (r i)) ℂ) (i : Fin t) :
  ‖CLM (M i)‖ ≤ ‖CLM (bDA r s M)‖ := by
 refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
 let b₀ : Fin (s i) := ⟨0, hs i⟩
 let v : EuclideanSpace ℂ (Σ k : Fin t, Fin (r k) × Fin (s k)) :=
  WithLp.toLp 2 fun ⟨k, a, b⟩ =>
   if hk : k = i then (if b = hk ▸ b₀ then w.ofLp (hk ▸ a) else 0) else 0
 have hv_norm : ‖v‖ = ‖w‖ := by
  have hsq : ‖v‖ ^ 2 = ‖w‖ ^ 2 := by
   rw [norm_sq_eq, norm_sq_eq, Fintype.sum_sigma,
    sum_eq_single i]
   ·
    simp only [v, ↓reduceDIte, sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_eq_single b₀]
    · simp
    · intro b _ hbb; simp [hbb]
    · intro h; exact absurd (mem_univ b₀) h
   · intro k _ hki; exact sum_eq_zero fun p _ => by simp [v, hki]
   · intro h; exact absurd (mem_univ i) h
  nlinarith [norm_nonneg v, norm_nonneg w]
 have hact_norm : ‖CLM (M i) w‖ ≤ ‖CLM (bDA r s M) v‖ := by
  have hsq : ‖CLM (M i) w‖ ^ 2 ≤ ‖CLM (bDA r s M) v‖ ^ 2 := by
   rw [norm_sq_eq, norm_sq_eq, Fintype.sum_sigma]
   refine le_trans ?_ (single_le_sum (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
    (mem_univ i))
   rw [sum_prod_type]
   refine sum_le_sum fun a _ => ?_
   refine le_trans ?_ (single_le_sum (fun _ _ => sq_nonneg _) (mem_univ b₀))
   have heq : (CLM (bDA r s M) v).ofLp ⟨i, a, b₀⟩ = (CLM (M i) w).ofLp a := by
    dsimp only [CLM]
    rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, mulVec, mulVec,
     dotProduct, dotProduct, Fintype.sum_sigma, sum_eq_single i]
    ·
     simp only [bDA, v, ↓reduceDIte, sum_prod_type]
     refine sum_congr rfl fun c _ => ?_
     rw [sum_eq_single b₀]
     · simp
     · intro b _ hbb; simp [hbb]
     · intro h; exact absurd (mem_univ b₀) h
    · intro k _ hki; exact sum_eq_zero fun p _ => by simp [bDA, Ne.symm hki]
    · intro h; exact absurd (mem_univ i) h
   rw [heq]
  nlinarith [norm_nonneg (CLM (M i) w), norm_nonneg (CLM (bDA r s M) v)]
 calc
  ‖CLM (M i) w‖ ≤ ‖CLM (bDA r s M) v‖ := hact_norm
  _ ≤ ‖CLM (bDA r s M)‖ * ‖v‖ := (CLM (bDA r s M)).le_opNorm v
  _ = ‖CLM (bDA r s M)‖ * ‖w‖ := by rw [hv_norm]
variable {n : Type*} [Fintype n] [DecidableEq n]
def bCEM {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (X : Matrix n n ℂ) (j : Fin bd.t) : Matrix (Fin (bd.r j)) (Fin (bd.r j)) ℂ :=
 fun a c => ((bd.s j : ℂ)⁻¹) * ∑ k : Fin (bd.s j), (bd.Uᴴ * X * bd.U) ⟨j, a, k⟩ ⟨j, c, k⟩
lemma condExp_eq_blockDiagA {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (X : Matrix n n ℂ) :
  cExp A X = bd.U * bDA bd.r bd.s (bCEM bd X) * bd.Uᴴ := by
 let Y : Matrix n n ℂ := bd.U * bDA bd.r bd.s (bCEM bd X) * bd.Uᴴ
 have hY_mem : Y ∈ A := by
  rw [bd.mem_iff]
  refine ⟨bCEM bd X, ?_⟩
  simp only [Y]
  calc
   bd.Uᴴ * (bd.U * bDA bd.r bd.s (bCEM bd X) * bd.Uᴴ) * bd.U
    = (bd.Uᴴ * bd.U) * bDA bd.r bd.s (bCEM bd X) * (bd.Uᴴ * bd.U) := by
      simp only [mma]
   _ = bDA bd.r bd.s (bCEM bd X) := by
      rw [bd.U_star_mul, m1m, mm1]
 apply condExp_eq_of_mem_of_orthog A hY_mem
 intro a ha
 obtain ⟨M, hM⟩ := (bd.mem_iff a).mp ha
 rw [ctS, sub_mul, trace_sub, sub_eq_zero]
 have htr : ∀ Z : Matrix n n ℂ, (Zᴴ * a).trace =
   ((bd.Uᴴ * Z * bd.U)ᴴ * bDA bd.r bd.s M).trace := by
  intro Z
  have hZ : (bd.Uᴴ * Z * bd.U)ᴴ = bd.Uᴴ * Zᴴ * bd.U := by
   simp only [ctM, ctct, mma]
  rw [hZ, ← hM]
  calc
   (Zᴴ * a).trace
    = ((Zᴴ * (bd.U * bd.Uᴴ) * a * bd.U) * bd.Uᴴ).trace := by
      simp only [mma, bd.U_mul_star, mm1]
   _ = (bd.Uᴴ * (Zᴴ * (bd.U * bd.Uᴴ) * a * bd.U)).trace := trace_mul_comm _ _
   _ = (bd.Uᴴ * Zᴴ * bd.U * (bd.Uᴴ * a * bd.U)).trace := by simp only [mma]
 rw [htr X, htr Y]
 have hY' : bd.Uᴴ * Y * bd.U = bDA bd.r bd.s (bCEM bd X) := by
  simp only [Y]
  calc
   bd.Uᴴ * (bd.U * bDA bd.r bd.s (bCEM bd X) * bd.Uᴴ) * bd.U
    = (bd.Uᴴ * bd.U) * bDA bd.r bd.s (bCEM bd X) * (bd.Uᴴ * bd.U) := by
      simp only [mma]
   _ = bDA bd.r bd.s (bCEM bd X) := by
      rw [bd.U_star_mul, m1m, mm1]
 rw [hY', blockDiagA_conjTranspose, blockDiagA_mul]
 rw [Matrix.trace, Matrix.trace, Fintype.sum_sigma, Fintype.sum_sigma]
 refine sum_congr rfl fun j _ => ?_
 rw [sum_prod_type, sum_prod_type]
 have hL : (∑ a' : Fin (bd.r j), ∑ k : Fin (bd.s j),
   Matrix.diag ((bd.Uᴴ * X * bd.U)ᴴ * bDA bd.r bd.s M) ⟨j, a', k⟩) =
   ∑ a' : Fin (bd.r j), ∑ c' : Fin (bd.r j),
    (∑ k : Fin (bd.s j), star ((bd.Uᴴ * X * bd.U) ⟨j, c', k⟩ ⟨j, a', k⟩)) * M j c' a' := by
  refine sum_congr rfl fun a' _ => ?_
  have hinner : ∀ k : Fin (bd.s j),
    Matrix.diag ((bd.Uᴴ * X * bd.U)ᴴ * bDA bd.r bd.s M) ⟨j, a', k⟩ =
    ∑ c' : Fin (bd.r j), star ((bd.Uᴴ * X * bd.U) ⟨j, c', k⟩ ⟨j, a', k⟩) * M j c' a' := by
   intro k
   rw [Matrix.diag_apply, mul_apply, Fintype.sum_sigma, sum_eq_single j]
   ·
    simp only [bDA, ↓reduceDIte, sum_prod_type]
    refine sum_congr rfl fun c' _ => ?_
    rw [sum_eq_single k]
    · simp
    · intro l _ hlk; simp [hlk]
    · intro h; exact absurd (mem_univ k) h
   · intro l _ hlj; exact sum_eq_zero fun p _ => by simp [bDA, hlj]
   · intro h; exact absurd (mem_univ j) h
  simp_rw [hinner]
  rw [sum_comm]
  refine sum_congr rfl fun c' _ => by rw [Finset.sum_mul]
 have hR : (∑ a' : Fin (bd.r j), ∑ k : Fin (bd.s j),
   Matrix.diag (bDA bd.r bd.s (fun l => (bCEM bd X l)ᴴ * M l)) ⟨j, a', k⟩) =
   ∑ a' : Fin (bd.r j), ∑ c' : Fin (bd.r j),
    (∑ k : Fin (bd.s j), star ((bd.Uᴴ * X * bd.U) ⟨j, c', k⟩ ⟨j, a', k⟩)) * M j c' a' := by
  refine sum_congr rfl fun a' _ => ?_
  simp only [Matrix.diag_apply, bDA, ↓reduceDIte, ↓reduceIte, sum_const,
   card_univ, card_fin, nsmul_eq_mul]
  rw [mul_apply, Finset.mul_sum]
  refine sum_congr rfl fun c' _ => ?_
  have hsj0 : (bd.s j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (bd.hs j))
  rw [ctA]
  dsimp only [bCEM]
  rw [star_mul', star_inv₀, star_def, map_natCast, ← star_def, star_sum,
   ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hsj0, one_mul]
 rw [hL, hR]
def cBlk {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (c : Matrix n n ℂ) (j : Fin bd.t) : Matrix (Fin (bd.s j)) (Fin (bd.s j)) ℂ :=
 fun b₁ b₂ => (bd.Uᴴ * c * bd.U) ⟨j, ⟨0, bd.hr j⟩, b₁⟩ ⟨j, ⟨0, bd.hr j⟩, b₂⟩
lemma commBlock_spec {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  {c : Matrix n n ℂ} (hc : c ∈ comm A) :
  bd.Uᴴ * c * bd.U = bDC bd.r bd.s (cBlk bd c) := by
 obtain ⟨N, hN⟩ := (bDec_comm_iff bd c).mp hc
 have hNeq : cBlk bd c = N := by
  funext j b₁ b₂
  have h := congrFun (congrFun hN ⟨j, ⟨0, bd.hr j⟩, b₁⟩) ⟨j, ⟨0, bd.hr j⟩, b₂⟩
  simpa [cBlk, bDC] using h
 rw [hNeq, hN]
lemma commBlock_one {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A) :
  cBlk bd 1 = fun _ => 1 := by
 funext j b₁ b₂
 simp only [cBlk, mm1, bd.U_star_mul, Matrix.one_apply, Sigma.mk.inj_iff,
  heq_eq_eq, Prod.mk.injEq, true_and]
lemma commBlock_add {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (c₁ c₂ : Matrix n n ℂ) :
  cBlk bd (c₁ + c₂) = fun j => cBlk bd c₁ j + cBlk bd c₂ j := by
 funext j b₁ b₂
 simp only [cBlk, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
lemma commBlock_smul {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (α : ℂ) (c : Matrix n n ℂ) :
  cBlk bd (α • c) = fun j => α • cBlk bd c j := by
 funext j b₁ b₂
 simp only [cBlk, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]
lemma commBlock_conjTranspose {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (c : Matrix n n ℂ) :
  cBlk bd cᴴ = fun j => (cBlk bd c j)ᴴ := by
 funext j b₁ b₂
 have h : (bd.Uᴴ * cᴴ * bd.U) = (bd.Uᴴ * c * bd.U)ᴴ := by
  simp only [ctM, ctct, mma]
 simp only [cBlk, h, ctA]
lemma commBlock_mul {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  {c₁ c₂ : Matrix n n ℂ} (hc₁ : c₁ ∈ comm A) (hc₂ : c₂ ∈ comm A) :
  cBlk bd (c₁ * c₂) = fun j => cBlk bd c₁ j * cBlk bd c₂ j := by
 have h1 := commBlock_spec bd hc₁
 have h2 := commBlock_spec bd hc₂
 have hmul : bd.Uᴴ * (c₁ * c₂) * bd.U =
   bDC bd.r bd.s (fun j => cBlk bd c₁ j * cBlk bd c₂ j) := by
  calc
   bd.Uᴴ * (c₁ * c₂) * bd.U
    = (bd.Uᴴ * c₁ * bd.U) * (bd.Uᴴ * c₂ * bd.U) := by
      calc
       bd.Uᴴ * (c₁ * c₂) * bd.U = bd.Uᴴ * c₁ * (bd.U * bd.Uᴴ) * c₂ * bd.U := by
          rw [bd.U_mul_star, mm1]; simp only [mma]
       _ = (bd.Uᴴ * c₁ * bd.U) * (bd.Uᴴ * c₂ * bd.U) := by simp only [mma]
   _ = bDC bd.r bd.s (fun j => cBlk bd c₁ j * cBlk bd c₂ j) := by
      rw [h1, h2, blockDiagC_mul]
 funext j b₁ b₂
 have h := congrFun (congrFun hmul ⟨j, ⟨0, bd.hr j⟩, b₁⟩) ⟨j, ⟨0, bd.hr j⟩, b₂⟩
 simpa [cBlk, bDC] using h
def cPr {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) : Matrix n n ℂ :=
 bd.U * bDA bd.r bd.s (fun k => if k = i then 1 else 0) * bd.Uᴴ
lemma centralProj_eq_blockDiagC {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) :
  cPr bd i = bd.U * bDC bd.r bd.s (fun k => if k = i then 1 else 0) * bd.Uᴴ := by
 unfold cPr
 congr 2
 ext ⟨j₁, a₁, b₁⟩ ⟨j₂, a₂, b₂⟩
 by_cases hj : j₁ = j₂
 ·
  subst hj
  by_cases hji : j₁ = i
  · subst hji; simp only [bDA, bDC, ↓reduceDIte, ↓reduceIte, Matrix.one_apply]; split_ifs <;> rfl
  · simp [bDA, bDC, hji]
 · simp [bDA, bDC, hj]
lemma centralProj_conj {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) :
  bd.Uᴴ * cPr bd i * bd.U = bDA bd.r bd.s (fun k => if k = i then 1 else 0) := by
 simp only [cPr]
 calc
  bd.Uᴴ * (bd.U * bDA bd.r bd.s (fun k => if k = i then 1 else 0) * bd.Uᴴ) * bd.U
   = (bd.Uᴴ * bd.U) * bDA bd.r bd.s (fun k => if k = i then 1 else 0) * (bd.Uᴴ * bd.U) := by
     simp only [mma]
  _ = bDA bd.r bd.s (fun k => if k = i then 1 else 0) := by
     rw [bd.U_star_mul, m1m, mm1]
lemma cPr_mem {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) : cPr bd i ∈ A :=
 (bd.mem_iff _).mpr ⟨_, centralProj_conj bd i⟩
lemma cPr_comm {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) : cPr bd i ∈ comm A := by
 rw [bDec_comm_iff bd]
 refine ⟨fun k => if k = i then 1 else 0, ?_⟩
 rw [centralProj_eq_blockDiagC]
 calc
  bd.Uᴴ * (bd.U * bDC bd.r bd.s (fun k => if k = i then 1 else 0) * bd.Uᴴ) * bd.U
   = (bd.Uᴴ * bd.U) * bDC bd.r bd.s (fun k => if k = i then 1 else 0) * (bd.Uᴴ * bd.U) := by
     simp only [mma]
  _ = bDC bd.r bd.s (fun k => if k = i then 1 else 0) := by
     rw [bd.U_star_mul, m1m, mm1]
lemma cPr_herm {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) : (cPr bd i)ᴴ = cPr bd i := by
 simp only [cPr, ctM, ctct,
  blockDiagA_conjTranspose, ← mma]
 apply congrArg (fun M => bd.U * bDA bd.r bd.s M * bd.Uᴴ)
 funext k; split_ifs <;> simp
lemma cPr_mul {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i j : Fin bd.t) :
  cPr bd i * cPr bd j = if i = j then cPr bd i else 0 := by
 simp only [cPr]
 calc
  (bd.U * bDA bd.r bd.s (fun k => if k = i then 1 else 0) * bd.Uᴴ) *
    (bd.U * bDA bd.r bd.s (fun k => if k = j then 1 else 0) * bd.Uᴴ)
   = bd.U * (bDA bd.r bd.s (fun k => if k = i then 1 else 0) *
     ((bd.Uᴴ * bd.U) * bDA bd.r bd.s (fun k => if k = j then 1 else 0))) * bd.Uᴴ := by
     simp only [mma]
  _ = bd.U * bDA bd.r bd.s
     (fun k => (if k = i then (1 : Matrix (Fin (bd.r k)) (Fin (bd.r k)) ℂ) else 0) *
      (if k = j then 1 else 0)) * bd.Uᴴ := by
     rw [bd.U_star_mul, m1m, blockDiagA_mul]
  _ = if i = j then bd.U * bDA bd.r bd.s (fun k => if k = i then 1 else 0) * bd.Uᴴ else 0 := by
     by_cases hij : i = j
     ·
      subst hij
      simp only [↓reduceIte]
      apply congrArg (fun M => bd.U * bDA bd.r bd.s M * bd.Uᴴ)
      funext k; split_ifs <;> simp
     ·
      simp only [if_neg hij]
      have h0 : bDA bd.r bd.s
        (fun k => (if k = i then (1 : Matrix (Fin (bd.r k)) (Fin (bd.r k)) ℂ) else 0) *
         (if k = j then 1 else 0)) = 0 := by
       ext ⟨k₁, a₁, b₁⟩ ⟨k₂, a₂, b₂⟩
       by_cases hk : k₁ = k₂
       ·
        subst hk
        by_cases hki : k₁ = i
        · subst hki; simp [bDA, hij]
        · simp [bDA, hki]
       · simp [bDA, hk]
      rw [h0, Matrix.mul_zero, Matrix.zero_mul]
lemma sum_cPr {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A) :
  ∑ i : Fin bd.t, cPr bd i = 1 := by
 simp only [cPr, ← Matrix.mul_sum, ← Matrix.sum_mul]
 have hsum : ∑ i : Fin bd.t, bDA bd.r bd.s (fun k => if k = i then 1 else 0) =
   bDA bd.r bd.s (fun _ => 1) := by
  ext ⟨k₁, a₁, b₁⟩ ⟨k₂, a₂, b₂⟩
  simp only [Matrix.sum_apply, bDA]
  by_cases hk : k₁ = k₂
  ·
   subst hk
   simp only [↓reduceDIte]
   by_cases hb : b₁ = b₂
   ·
    subst hb
    simp only [↓reduceIte]
    rw [sum_eq_single k₁]
    · simp
    · intro i _ hik; simp [hik.symm]
    · intro h; exact absurd (mem_univ k₁) h
   · simp [hb]
  · simp [hk]
 rw [hsum, blockDiagA_one, mm1, bd.U_mul_star]
lemma trace_centralProj {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) : (cPr bd i).trace = ((bd.r i * bd.s i : ℕ) : ℂ) := by
 simp only [cPr]
 rw [Matrix.trace_mul_cycle, bd.U_star_mul, m1m, Matrix.trace, Fintype.sum_sigma,
  sum_eq_single i]
 · simp [bDA]
 · intro k _ hki; exact sum_eq_zero fun p _ => by simp [bDA, hki]
 · intro h; exact absurd (mem_univ i) h
def mUA {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) (a c : Fin (bd.r i)) : Matrix n n ℂ :=
 bd.U * bDA bd.r bd.s (fun k => if hk : k = i then hk ▸ Matrix.single a c 1 else 0) * bd.Uᴴ
lemma matUnitA_conj {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) (a c : Fin (bd.r i)) :
  bd.Uᴴ * mUA bd i a c * bd.U =
   bDA bd.r bd.s (fun k => if hk : k = i then hk ▸ Matrix.single a c 1 else 0) := by
 let F : (k : Fin bd.t) → Matrix (Fin (bd.r k)) (Fin (bd.r k)) ℂ :=
  fun k => if hk : k = i then hk ▸ Matrix.single a c 1 else 0
 change bd.Uᴴ * (bd.U * bDA bd.r bd.s F * bd.Uᴴ) * bd.U = bDA bd.r bd.s F
 calc
  bd.Uᴴ * (bd.U * bDA bd.r bd.s F * bd.Uᴴ) * bd.U
   = (bd.Uᴴ * bd.U) * bDA bd.r bd.s F * (bd.Uᴴ * bd.U) := by simp only [mma]
  _ = bDA bd.r bd.s F := by rw [bd.U_star_mul, m1m, mm1]
lemma mUA_mem {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) (a c : Fin (bd.r i)) : mUA bd i a c ∈ A :=
 (bd.mem_iff _).mpr ⟨_, matUnitA_conj bd i a c⟩
lemma matUnitA_conjTranspose {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) (a c : Fin (bd.r i)) : (mUA bd i a c)ᴴ = mUA bd i c a := by
 simp only [mUA, ctM, ctct,
  blockDiagA_conjTranspose, ← mma]
 apply congrArg (fun M => bd.U * bDA bd.r bd.s M * bd.Uᴴ)
 funext k
 by_cases hk : k = i
 ·
  subst hk
  simp only [↓reduceDIte]
  ext x y
  simp only [ctA, Matrix.single_apply, and_comm]
  split_ifs <;> simp
 · simp [hk]
lemma mUA_mul {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) (a b c d : Fin (bd.r i)) :
  mUA bd i a b * mUA bd i c d = if b = c then mUA bd i a d else 0 := by
 let F1 : (k : Fin bd.t) → Matrix (Fin (bd.r k)) (Fin (bd.r k)) ℂ :=
  fun k => if hk : k = i then hk ▸ Matrix.single a b 1 else 0
 let F2 : (k : Fin bd.t) → Matrix (Fin (bd.r k)) (Fin (bd.r k)) ℂ :=
  fun k => if hk : k = i then hk ▸ Matrix.single c d 1 else 0
 change (bd.U * bDA bd.r bd.s F1 * bd.Uᴴ) * (bd.U * bDA bd.r bd.s F2 * bd.Uᴴ) = _
 calc
  (bd.U * bDA bd.r bd.s F1 * bd.Uᴴ) * (bd.U * bDA bd.r bd.s F2 * bd.Uᴴ)
   = bd.U * (bDA bd.r bd.s F1 * ((bd.Uᴴ * bd.U) * bDA bd.r bd.s F2)) * bd.Uᴴ := by
     simp only [mma]
  _ = bd.U * bDA bd.r bd.s (fun k => F1 k * F2 k) * bd.Uᴴ := by
     rw [bd.U_star_mul, m1m, blockDiagA_mul]
  _ = if b = c then mUA bd i a d else 0 := by
     by_cases hbc : b = c
     ·
      subst hbc
      simp only [↓reduceIte, mUA]
      apply congrArg (fun M => bd.U * bDA bd.r bd.s M * bd.Uᴴ)
      funext k
      by_cases hk : k = i
      · subst hk; simp [F1, F2, Matrix.single_mul_single_same]
      · simp [F1, F2, hk]
     ·
      simp only [if_neg hbc]
      have h0 : bDA bd.r bd.s (fun k => F1 k * F2 k) = 0 := by
       ext ⟨k₁, x₁, y₁⟩ ⟨k₂, x₂, y₂⟩
       by_cases hk : k₁ = k₂
       ·
        subst hk
        by_cases hki : k₁ = i
        ·
         subst hki
         have hzero : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 = 0 := by
          ext r s
          rw [mul_apply, Matrix.zero_apply]
          exact sum_eq_zero fun l _ => by
           by_cases hlb : l = b
           · subst hlb; simp [Matrix.single_apply, Ne.symm hbc]
           · simp [Matrix.single_apply, Ne.symm hlb]
         simp [bDA, F1, F2, hzero]
        · simp [bDA, F1, F2, hki]
       · simp [bDA, hk]
      rw [h0, Matrix.mul_zero, Matrix.zero_mul]
lemma matUnitA_mul_ne {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  {i j : Fin bd.t} (hij : i ≠ j) (a b : Fin (bd.r i)) (c d : Fin (bd.r j)) :
  mUA bd i a b * mUA bd j c d = 0 := by
 let F1 : (k : Fin bd.t) → Matrix (Fin (bd.r k)) (Fin (bd.r k)) ℂ :=
  fun k => if hk : k = i then hk ▸ Matrix.single a b 1 else 0
 let F2 : (k : Fin bd.t) → Matrix (Fin (bd.r k)) (Fin (bd.r k)) ℂ :=
  fun k => if hk : k = j then hk ▸ Matrix.single c d 1 else 0
 change (bd.U * bDA bd.r bd.s F1 * bd.Uᴴ) * (bd.U * bDA bd.r bd.s F2 * bd.Uᴴ) = 0
 calc
  (bd.U * bDA bd.r bd.s F1 * bd.Uᴴ) * (bd.U * bDA bd.r bd.s F2 * bd.Uᴴ)
   = bd.U * (bDA bd.r bd.s F1 * ((bd.Uᴴ * bd.U) * bDA bd.r bd.s F2)) * bd.Uᴴ := by
     simp only [mma]
  _ = bd.U * bDA bd.r bd.s (fun k => F1 k * F2 k) * bd.Uᴴ := by
     rw [bd.U_star_mul, m1m, blockDiagA_mul]
  _ = 0 := by
     have h0 : bDA bd.r bd.s (fun k => F1 k * F2 k) = 0 := by
      ext ⟨k₁, x₁, y₁⟩ ⟨k₂, x₂, y₂⟩
      by_cases hk : k₁ = k₂
      ·
       subst hk
       by_cases hki : k₁ = i
       · subst hki; simp [bDA, F1, F2, hij]
       · simp [bDA, F1, F2, hki]
      · simp [bDA, hk]
     rw [h0, Matrix.mul_zero, Matrix.zero_mul]
lemma sum_matUnitA_diag {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) : ∑ a : Fin (bd.r i), mUA bd i a a = cPr bd i := by
 simp only [mUA, cPr, ← Matrix.mul_sum, ← Matrix.sum_mul]
 congr 2
 ext ⟨k₁, x₁, y₁⟩ ⟨k₂, x₂, y₂⟩
 simp only [Matrix.sum_apply, bDA]
 by_cases hk : k₁ = k₂
 ·
  subst hk
  simp only [↓reduceDIte]
  by_cases hy : y₁ = y₂
  ·
   subst hy
   simp only [↓reduceIte]
   by_cases hki : k₁ = i
   ·
    subst hki
    simp only [↓reduceDIte, ↓reduceIte, Matrix.one_apply, Matrix.single_apply]
    by_cases hx : x₁ = x₂
    ·
     subst hx
     rw [sum_eq_single x₁]
     · simp
     · intro a _ hax; simp [hax]
     · intro h; exact absurd (mem_univ x₁) h
    ·
     rw [if_neg hx]
     exact sum_eq_zero fun a _ => by
      by_cases hxa : a = x₁
      · subst hxa; simp [hx]
      · simp [hxa]
   · simp [hki]
  · simp [hy]
 · simp [hk]
lemma trace_matUnitA_diag {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) (a : Fin (bd.r i)) : (mUA bd i a a).trace = (bd.s i : ℂ) := by
 simp only [mUA]
 rw [Matrix.trace_mul_cycle, bd.U_star_mul, m1m, Matrix.trace, Fintype.sum_sigma,
  sum_eq_single i]
 ·
  simp only [Matrix.diag_apply, bDA, ↓reduceDIte, ↓reduceIte, sum_prod_type]
  rw [sum_eq_single a]
  · simp
  · intro x _ hxa; exact sum_eq_zero fun _ _ => by simp [hxa.symm]
  · intro h; exact absurd (mem_univ a) h
 · intro k _ hki; exact sum_eq_zero fun p _ => by simp [bDA, hki]
 · intro h; exact absurd (mem_univ i) h
def mUC {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) (b d : Fin (bd.s i)) : Matrix n n ℂ :=
 bd.U * bDC bd.r bd.s (fun k => if hk : k = i then hk ▸ Matrix.single b d 1 else 0) * bd.Uᴴ
lemma matUnitC_conj {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) (b d : Fin (bd.s i)) :
  bd.Uᴴ * mUC bd i b d * bd.U =
   bDC bd.r bd.s (fun k => if hk : k = i then hk ▸ Matrix.single b d 1 else 0) := by
 let F : (k : Fin bd.t) → Matrix (Fin (bd.s k)) (Fin (bd.s k)) ℂ :=
  fun k => if hk : k = i then hk ▸ Matrix.single b d 1 else 0
 change bd.Uᴴ * (bd.U * bDC bd.r bd.s F * bd.Uᴴ) * bd.U = bDC bd.r bd.s F
 calc
  bd.Uᴴ * (bd.U * bDC bd.r bd.s F * bd.Uᴴ) * bd.U
   = (bd.Uᴴ * bd.U) * bDC bd.r bd.s F * (bd.Uᴴ * bd.U) := by simp only [mma]
  _ = bDC bd.r bd.s F := by rw [bd.U_star_mul, m1m, mm1]
lemma matUnitC_mem {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) (b d : Fin (bd.s i)) : mUC bd i b d ∈ comm A :=
 (bDec_comm_iff bd _).mpr ⟨_, matUnitC_conj bd i b d⟩
lemma matUnitC_conjTranspose {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) (b d : Fin (bd.s i)) : (mUC bd i b d)ᴴ = mUC bd i d b := by
 simp only [mUC, ctM, ctct,
  blockDiagC_conjTranspose, ← mma]
 apply congrArg (fun M => bd.U * bDC bd.r bd.s M * bd.Uᴴ)
 funext k
 by_cases hk : k = i
 ·
  subst hk
  simp only [↓reduceDIte]
  ext x y
  simp only [ctA, Matrix.single_apply, and_comm]
  split_ifs <;> simp
 · simp [hk]
lemma matUnitC_mul_same {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) (b₁ b₂ b₃ b₄ : Fin (bd.s i)) :
  mUC bd i b₁ b₂ * mUC bd i b₃ b₄ = if b₂ = b₃ then mUC bd i b₁ b₄ else 0 := by
 let F1 : (k : Fin bd.t) → Matrix (Fin (bd.s k)) (Fin (bd.s k)) ℂ :=
  fun k => if hk : k = i then hk ▸ Matrix.single b₁ b₂ 1 else 0
 let F2 : (k : Fin bd.t) → Matrix (Fin (bd.s k)) (Fin (bd.s k)) ℂ :=
  fun k => if hk : k = i then hk ▸ Matrix.single b₃ b₄ 1 else 0
 change (bd.U * bDC bd.r bd.s F1 * bd.Uᴴ) * (bd.U * bDC bd.r bd.s F2 * bd.Uᴴ) = _
 calc
  (bd.U * bDC bd.r bd.s F1 * bd.Uᴴ) * (bd.U * bDC bd.r bd.s F2 * bd.Uᴴ)
   = bd.U * (bDC bd.r bd.s F1 * ((bd.Uᴴ * bd.U) * bDC bd.r bd.s F2)) * bd.Uᴴ := by
     simp only [mma]
  _ = bd.U * bDC bd.r bd.s (fun k => F1 k * F2 k) * bd.Uᴴ := by
     rw [bd.U_star_mul, m1m, blockDiagC_mul]
  _ = if b₂ = b₃ then mUC bd i b₁ b₄ else 0 := by
     by_cases hbc : b₂ = b₃
     ·
      subst hbc
      simp only [↓reduceIte, mUC]
      apply congrArg (fun M => bd.U * bDC bd.r bd.s M * bd.Uᴴ)
      funext k
      by_cases hk : k = i
      · subst hk; simp [F1, F2, Matrix.single_mul_single_same]
      · simp [F1, F2, hk]
     ·
      simp only [if_neg hbc]
      have h0 : bDC bd.r bd.s (fun k => F1 k * F2 k) = 0 := by
       ext ⟨k₁, x₁, y₁⟩ ⟨k₂, x₂, y₂⟩
       by_cases hk : k₁ = k₂
       ·
        subst hk
        by_cases hki : k₁ = i
        ·
         subst hki
         have hzero : Matrix.single b₁ b₂ (1 : ℂ) * Matrix.single b₃ b₄ 1 = 0 := by
          ext r s
          rw [mul_apply, Matrix.zero_apply]
          exact sum_eq_zero fun l _ => by
           by_cases hlb : l = b₂
           · subst hlb; simp [Matrix.single_apply, Ne.symm hbc]
           · simp [Matrix.single_apply, Ne.symm hlb]
         simp [bDC, F1, F2, hzero]
        · simp [bDC, F1, F2, hki]
       · simp [bDC, hk]
      rw [h0, Matrix.mul_zero, Matrix.zero_mul]
lemma matUnitC_mul_ne {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  {i j : Fin bd.t} (hij : i ≠ j) (b₁ b₂ : Fin (bd.s i)) (b₃ b₄ : Fin (bd.s j)) :
  mUC bd i b₁ b₂ * mUC bd j b₃ b₄ = 0 := by
 let F1 : (k : Fin bd.t) → Matrix (Fin (bd.s k)) (Fin (bd.s k)) ℂ :=
  fun k => if hk : k = i then hk ▸ Matrix.single b₁ b₂ 1 else 0
 let F2 : (k : Fin bd.t) → Matrix (Fin (bd.s k)) (Fin (bd.s k)) ℂ :=
  fun k => if hk : k = j then hk ▸ Matrix.single b₃ b₄ 1 else 0
 change (bd.U * bDC bd.r bd.s F1 * bd.Uᴴ) * (bd.U * bDC bd.r bd.s F2 * bd.Uᴴ) = 0
 calc
  (bd.U * bDC bd.r bd.s F1 * bd.Uᴴ) * (bd.U * bDC bd.r bd.s F2 * bd.Uᴴ)
   = bd.U * (bDC bd.r bd.s F1 * ((bd.Uᴴ * bd.U) * bDC bd.r bd.s F2)) * bd.Uᴴ := by
     simp only [mma]
  _ = bd.U * bDC bd.r bd.s (fun k => F1 k * F2 k) * bd.Uᴴ := by
     rw [bd.U_star_mul, m1m, blockDiagC_mul]
  _ = 0 := by
     have h0 : bDC bd.r bd.s (fun k => F1 k * F2 k) = 0 := by
      ext ⟨k₁, x₁, y₁⟩ ⟨k₂, x₂, y₂⟩
      by_cases hk : k₁ = k₂
      ·
       subst hk
       by_cases hki : k₁ = i
       · subst hki; simp [bDC, F1, F2, hij]
       · simp [bDC, F1, F2, hki]
      · simp [bDC, hk]
     rw [h0, Matrix.mul_zero, Matrix.zero_mul]
lemma sum_matUnitC_diag {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  (i : Fin bd.t) : ∑ b : Fin (bd.s i), mUC bd i b b = cPr bd i := by
 rw [centralProj_eq_blockDiagC]
 simp only [mUC, ← Matrix.mul_sum, ← Matrix.sum_mul]
 congr 2
 ext ⟨k₁, x₁, y₁⟩ ⟨k₂, x₂, y₂⟩
 simp only [Matrix.sum_apply, bDC]
 by_cases hk : k₁ = k₂
 ·
  subst hk
  simp only [↓reduceDIte]
  by_cases hx : x₁ = x₂
  ·
   subst hx
   simp only [↓reduceIte]
   by_cases hki : k₁ = i
   ·
    subst hki
    simp only [↓reduceDIte, ↓reduceIte, Matrix.one_apply, Matrix.single_apply]
    by_cases hy : y₁ = y₂
    ·
     subst hy
     rw [sum_eq_single y₁]
     · simp
     · intro b _ hby; simp [hby]
     · intro h; exact absurd (mem_univ y₁) h
    ·
     rw [if_neg hy]
     exact sum_eq_zero fun b _ => by
      by_cases hby : b = y₁
      · subst hby; simp [hy]
      · simp [hby]
   · simp [hki]
  · simp [hx]
 · simp [hk]
lemma expand_in_matUnitA {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  {a : Matrix n n ℂ} (ha : a ∈ A) :
  ∃ M : (i : Fin bd.t) → Matrix (Fin (bd.r i)) (Fin (bd.r i)) ℂ,
   bd.Uᴴ * a * bd.U = bDA bd.r bd.s M ∧
   a = ∑ i : Fin bd.t, ∑ x : Fin (bd.r i), ∑ y : Fin (bd.r i), M i x y • mUA bd i x y := by
 obtain ⟨M, hM⟩ := (bd.mem_iff a).mp ha
 refine ⟨M, hM, ?_⟩
 have ha_eq : a = bd.U * bDA bd.r bd.s M * bd.Uᴴ := by
  calc
   a = (bd.U * bd.Uᴴ) * a * (bd.U * bd.Uᴴ) := by rw [bd.U_mul_star, m1m, mm1]
   _ = bd.U * (bd.Uᴴ * a * bd.U) * bd.Uᴴ := by simp only [mma]
   _ = bd.U * bDA bd.r bd.s M * bd.Uᴴ := by rw [hM]
 rw [ha_eq]
 have hterm : ∀ (i : Fin bd.t) (x y : Fin (bd.r i)),
   M i x y • mUA bd i x y =
    bd.U * (M i x y • bDA bd.r bd.s (fun k => if hk : k = i then hk ▸ Matrix.single x y 1 else 0)) * bd.Uᴴ := by
  intro i x y
  simp only [mUA]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]
 simp_rw [hterm]
 simp only [← Matrix.mul_sum, ← Matrix.sum_mul]
 apply congrArg (fun D => bd.U * D * bd.Uᴴ)
 ext ⟨k₁, x₁, y₁⟩ ⟨k₂, x₂, y₂⟩
 simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, bDA]
 by_cases hk : k₁ = k₂
 ·
  subst hk
  simp only [↓reduceDIte]
  by_cases hy : y₁ = y₂
  ·
   subst hy
   simp only [↓reduceIte]
   rw [sum_eq_single k₁]
   ·
    simp only [↓reduceDIte]
    rw [sum_eq_single x₁]
    ·
     rw [sum_eq_single x₂]
     · simp
     · intro y _ hyx; simp [hyx]
     · intro h; exact absurd (mem_univ x₂) h
    ·
     intro x _ hxx
     exact sum_eq_zero fun y _ => by simp [hxx]
    · intro h; exact absurd (mem_univ x₁) h
   ·
    intro i _ hik
    exact sum_eq_zero fun x _ => sum_eq_zero fun y _ => by simp [Ne.symm hik]
   · intro h; exact absurd (mem_univ k₁) h
  · simp [hy]
 · simp [hk]
lemma expand_in_matUnitC {A : StarSubalgebra ℂ (Matrix n n ℂ)} (bd : BDec A)
  {c : Matrix n n ℂ} (hc : c ∈ comm A) :
  ∃ N : (i : Fin bd.t) → Matrix (Fin (bd.s i)) (Fin (bd.s i)) ℂ,
   bd.Uᴴ * c * bd.U = bDC bd.r bd.s N ∧
   c = ∑ i : Fin bd.t, ∑ b₁ : Fin (bd.s i), ∑ b₂ : Fin (bd.s i), N i b₁ b₂ • mUC bd i b₁ b₂ := by
 obtain ⟨N, hN⟩ := (bDec_comm_iff bd c).mp hc
 refine ⟨N, hN, ?_⟩
 have hc_eq : c = bd.U * bDC bd.r bd.s N * bd.Uᴴ := by
  calc
   c = (bd.U * bd.Uᴴ) * c * (bd.U * bd.Uᴴ) := by rw [bd.U_mul_star, m1m, mm1]
   _ = bd.U * (bd.Uᴴ * c * bd.U) * bd.Uᴴ := by simp only [mma]
   _ = bd.U * bDC bd.r bd.s N * bd.Uᴴ := by rw [hN]
 rw [hc_eq]
 have hterm : ∀ (i : Fin bd.t) (b₁ b₂ : Fin (bd.s i)),
   N i b₁ b₂ • mUC bd i b₁ b₂ =
    bd.U * (N i b₁ b₂ • bDC bd.r bd.s (fun k => if hk : k = i then hk ▸ Matrix.single b₁ b₂ 1 else 0)) * bd.Uᴴ := by
  intro i b₁ b₂
  simp only [mUC]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]
 simp_rw [hterm]
 simp only [← Matrix.mul_sum, ← Matrix.sum_mul]
 apply congrArg (fun D => bd.U * D * bd.Uᴴ)
 ext ⟨k₁, x₁, y₁⟩ ⟨k₂, x₂, y₂⟩
 simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, bDC]
 by_cases hk : k₁ = k₂
 ·
  subst hk
  simp only [↓reduceDIte]
  by_cases hx : x₁ = x₂
  ·
   subst hx
   simp only [↓reduceIte]
   rw [sum_eq_single k₁]
   ·
    simp only [↓reduceDIte]
    rw [sum_eq_single y₁]
    ·
     rw [sum_eq_single y₂]
     · simp
     · intro b₂ _ hb; simp [hb]
     · intro h; exact absurd (mem_univ y₂) h
    ·
     intro b₁ _ hb
     exact sum_eq_zero fun b₂ _ => by simp [hb]
    · intro h; exact absurd (mem_univ y₁) h
   ·
    intro i _ hik
    exact sum_eq_zero fun b₁ _ => sum_eq_zero fun b₂ _ => by simp [Ne.symm hik]
   · intro h; exact absurd (mem_univ k₁) h
  · simp [hx]
 · simp [hk]
/- Projection eigenvalues, trace, rank, and isometric range embedding -/
lemma proj_eigenvalues_zero_or_one {P : Matrix n n ℂ}
  (hPh : P.IsHermitian) (hPp : P * P = P) (i : n) :
  hPh.eigenvalues i = 0 ∨ hPh.eigenvalues i = 1 := by
 have hid : hPh.cfc (fun t => t) = P := cfc_id hPh
 have hsq : hPh.cfc (fun t => t * t) = hPh.cfc (fun t => t) := by
  rw [← cfc_mul, hid, hPp]
 have hev : (hPh.cfc (fun t => t * t) - hPh.cfc (fun t => t)) = 0 := sub_eq_zero.mpr hsq
 have h0 := hsSq_cfc hPh (fun t => t * t - t)
 rw [← cfc_sub, hev, show hsSq (0 : Matrix n n ℂ) = 0 by simp [hsSq]] at h0
 have hi : (hPh.eigenvalues i * hPh.eigenvalues i - hPh.eigenvalues i) ^ 2 = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h0.symm i (mem_univ i)
 have h1 : hPh.eigenvalues i * (hPh.eigenvalues i - 1) = 0 := by nlinarith
 rcases mul_eq_zero.mp h1 with h | h
 · exact Or.inl h
 · exact Or.inr (sub_eq_zero.mp h)
lemma proj_trace_eq_card_nonzero {P : Matrix n n ℂ}
  (hPh : P.IsHermitian) (hPp : P * P = P) :
  P.trace = ((univ.filter fun i : n => hPh.eigenvalues i ≠ 0).card : ℂ) := by
 have htr_id : P.trace = ∑ i : n, ((hPh.eigenvalues i : ℝ) : ℂ) := by
  conv_lhs => rw [← cfc_id hPh]
  rw [trace_cfc]
  rfl
 rw [htr_id, ← sum_filter_add_sum_filter_not univ (fun i => hPh.eigenvalues i ≠ 0)]
 have h1 : ∑ i ∈ univ.filter (fun i => hPh.eigenvalues i ≠ 0), ((hPh.eigenvalues i : ℝ) : ℂ) =
   ((univ.filter fun i => hPh.eigenvalues i ≠ 0).card : ℂ) := by
  have : ∀ i ∈ univ.filter (fun i => hPh.eigenvalues i ≠ 0),
    ((hPh.eigenvalues i : ℝ) : ℂ) = 1 := by
   intro i hi
   rcases proj_eigenvalues_zero_or_one hPh hPp i with h0 | h1
   · exact absurd h0 (mem_filter.mp hi).2
   · simp [h1]
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_one]
 have h2 : ∑ i ∈ univ.filter (fun i => ¬ hPh.eigenvalues i ≠ 0),
   ((hPh.eigenvalues i : ℝ) : ℂ) = 0 := by
  refine sum_eq_zero fun i hi => ?_
  have h0 : hPh.eigenvalues i = 0 := not_not.mp (mem_filter.mp hi).2
  simp [h0]
 rw [h1, h2, add_zero]
lemma proj_trace_eq_finrank_range {P : Matrix n n ℂ}
  (hPh : P.IsHermitian) (hPp : P * P = P) :
  P.trace = (Module.finrank ℂ (LinearMap.range (CLM P).toLinearMap) : ℂ) := by
 classical
 let S := univ.filter fun i : n => hPh.eigenvalues i ≠ 0
 have hrange : LinearMap.range (CLM P).toLinearMap =
   Submodule.span ℂ (Set.range fun i : {i // i ∈ S} => hPh.eigenvectorBasis i.1) := by
  apply le_antisymm
  ·
   rintro _ ⟨v, rfl⟩
   have hrepr := (hPh.eigenvectorBasis.sum_repr' v).symm
   have hact : ∀ i : n, CLM P (hPh.eigenvectorBasis i) =
     (hPh.eigenvalues i : ℂ) • hPh.eigenvectorBasis i := by
    intro i
    apply WithLp.ofLp_injective
    simpa [ofLp_toEuclideanCLM, RCLike.real_smul_eq_coe_smul] using
     hPh.mulVec_eigenvectorBasis i
   change CLM P v ∈ _
   have hv_eq : CLM P v =
     CLM P (∑ i : n, ⟪hPh.eigenvectorBasis i, v⟫_ℂ • hPh.eigenvectorBasis i) := by
    rw [← hrepr]
   rw [hv_eq, map_sum]
   simp_rw [map_smul, hact]
   rw [← sum_filter_add_sum_filter_not univ (fun i => hPh.eigenvalues i ≠ 0)]
   have hrest : ∑ i ∈ univ.filter (fun i => ¬ hPh.eigenvalues i ≠ 0),
     ⟪hPh.eigenvectorBasis i, v⟫_ℂ • ((hPh.eigenvalues i : ℂ) • hPh.eigenvectorBasis i) = 0 := by
    refine sum_eq_zero fun i hi => ?_
    have h0 : hPh.eigenvalues i = 0 := not_not.mp (mem_filter.mp hi).2
    simp [h0]
   rw [hrest, add_zero]
   exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩))
  ·
   refine Submodule.span_le.mpr ?_
   rintro _ ⟨⟨i, hi⟩, rfl⟩
   refine ⟨hPh.eigenvectorBasis i, ?_⟩
   change CLM P (hPh.eigenvectorBasis i) = hPh.eigenvectorBasis i
   have h1 : hPh.eigenvalues i = 1 :=
    (proj_eigenvalues_zero_or_one hPh hPp i).resolve_left (mem_filter.mp hi).2
   apply WithLp.ofLp_injective
   rw [ofLp_toEuclideanCLM, hPh.mulVec_eigenvectorBasis i, h1, one_smul]
 rw [hrange]
 have hli : LinearIndependent ℂ (fun i : {i // i ∈ S} => hPh.eigenvectorBasis i.1) :=
  hPh.eigenvectorBasis.toBasis.linearIndependent.comp _ Subtype.val_injective
 rw [finrank_span_eq_card hli, Fintype.card_coe]
 exact proj_trace_eq_card_nonzero hPh hPp
lemma proj_trace_eq_finrank_mulVecLin {P : Matrix n n ℂ}
  (hPh : P.IsHermitian) (hPp : P * P = P) :
  P.trace = (Module.finrank ℂ (LinearMap.range (mulVecLin P)) : ℂ) := by
 rw [proj_trace_eq_finrank_range hPh hPp]
 congr 1
 let e : EuclideanSpace ℂ n ≃ₗ[ℂ] (n → ℂ) := WithLp.linearEquiv 2 ℂ (n → ℂ)
 have hcomm : (mulVecLin P).comp e.toLinearMap =
   e.toLinearMap.comp (CLM P).toLinearMap := by
  ext v i
  change P.mulVec v.ofLp i = (CLM P v).ofLp i
  dsimp only [CLM]
  rw [ofLp_toEuclideanCLM]
 have hrange : LinearMap.range (mulVecLin P) =
   Submodule.map e.toLinearMap (LinearMap.range (CLM P).toLinearMap) := by
  rw [← LinearMap.range_comp, ← hcomm, LinearMap.range_comp,
   LinearEquiv.range, Submodule.map_top]
 rw [hrange, LinearEquiv.finrank_map_eq]
omit [DecidableEq n] in
lemma proj_eq_zero_of_trace_re_zero {P : Matrix n n ℂ}
  (hPh : P.IsHermitian) (hPp : P * P = P) (h0 : (P.trace).re = 0) : P = 0 := by
 apply (hsSq_eq_zero_iff P).mp
 rw [hsSq_tr, hPh.eq, hPp, h0]
lemma exists_isometry_of_proj {K : Type*} [Fintype K] [DecidableEq K]
  {Q : Matrix K K ℂ} (hQh : Q.IsHermitian) (hQp : Q * Q = Q) :
  ∃ (m : ℕ) (ι : Matrix K (Fin m) ℂ),
   ιᴴ * ι = 1 ∧ ι * ιᴴ = Q ∧ (m : ℝ) = (Q.trace).re := by
 classical
 let S := univ.filter fun α : K => hQh.eigenvalues α ≠ 0
 let m := S.card
 let eS : Fin m ≃ {α : K // α ∈ S} := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
 let ι : Matrix K (Fin m) ℂ := fun x j => (hQh.eigenvectorBasis (eS j).1).ofLp x
 have hι_star : ιᴴ * ι = 1 := by
  ext j₁ j₂
  rw [mul_apply, Matrix.one_apply]
  have h1 : ∑ x : K, (ιᴴ) j₁ x * ι x j₂ =
    ⟪hQh.eigenvectorBasis (eS j₁).1, hQh.eigenvectorBasis (eS j₂).1⟫_ℂ := by
   rw [inner_eq_star_dotProduct, dotProduct]
   refine sum_congr rfl fun x _ => ?_
   rw [ctA, Pi.star_apply, mul_comm]
  rw [h1, (orthonormal_iff_ite.mp hQh.eigenvectorBasis.orthonormal) (eS j₁).1 (eS j₂).1]
  by_cases h : j₁ = j₂
  · subst h; simp
  ·
   have hne : (eS j₁).1 ≠ (eS j₂).1 := fun heq => h (eS.injective (Subtype.ext heq))
   simp [h, hne]
 have hι_mul : ι * ιᴴ = Q := by
  apply (toEuclideanCLM (n := K) (𝕜 := ℂ)).injective
  apply ContinuousLinearMap.ext
  intro v
  have hv := (hQh.eigenvectorBasis.sum_repr' v).symm
  have hactQ : CLM Q v = ∑ α ∈ S, ⟪hQh.eigenvectorBasis α, v⟫_ℂ • hQh.eigenvectorBasis α := by
   conv_lhs => rw [hv]
   rw [map_sum]
   have hvec : ∀ α : K, CLM Q (⟪hQh.eigenvectorBasis α, v⟫_ℂ • hQh.eigenvectorBasis α) =
     ⟪hQh.eigenvectorBasis α, v⟫_ℂ • ((hQh.eigenvalues α : ℂ) • hQh.eigenvectorBasis α) := by
    intro α
    rw [map_smul]
    congr 1
    apply WithLp.ofLp_injective
    simpa [ofLp_toEuclideanCLM, RCLike.real_smul_eq_coe_smul] using
     hQh.mulVec_eigenvectorBasis α
   simp_rw [hvec]
   rw [← sum_filter_add_sum_filter_not univ (fun α => hQh.eigenvalues α ≠ 0)]
   have hrest : ∑ α ∈ univ.filter (fun α => ¬ hQh.eigenvalues α ≠ 0),
     ⟪hQh.eigenvectorBasis α, v⟫_ℂ • ((hQh.eigenvalues α : ℂ) • hQh.eigenvectorBasis α) = 0 := by
    refine sum_eq_zero fun α hα => ?_
    have h0 : hQh.eigenvalues α = 0 := not_not.mp (mem_filter.mp hα).2
    simp [h0]
   rw [hrest, add_zero]
   refine sum_congr rfl fun α hα => ?_
   have h1 : hQh.eigenvalues α = 1 :=
    (proj_eigenvalues_zero_or_one hQh hQp α).resolve_left (mem_filter.mp hα).2
   simp [h1]
  have hactι : CLM (ι * ιᴴ) v =
    ∑ j : Fin m, ⟪hQh.eigenvectorBasis (eS j).1, v⟫_ℂ • hQh.eigenvectorBasis (eS j).1 := by
   apply WithLp.ofLp_injective; ext x
   dsimp only [CLM]
   rw [ofLp_toEuclideanCLM, mulVec, dotProduct]
   simp only [mul_apply, ctA, Finset.sum_mul,
    WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
   rw [sum_comm]
   refine sum_congr rfl fun j _ => ?_
   rw [inner_eq_star_dotProduct, dotProduct, Finset.sum_mul]
   refine sum_congr rfl fun y _ => by simp only [Pi.star_apply, ι]; ring
  change CLM (ι * ιᴴ) v = CLM Q v
  rw [hactι, hactQ]
  rw [← sum_attach S (fun α => ⟪hQh.eigenvectorBasis α, v⟫_ℂ • hQh.eigenvectorBasis α)]
  exact Fintype.sum_bijective eS eS.bijective _ _ fun _ => rfl
 refine ⟨m, ι, hι_star, hι_mul, ?_⟩
 have htr := proj_trace_eq_card_nonzero hQh hQp
 have hre := congrArg Complex.re htr
 simpa [m, S] using hre.symm
lemma finrank_range_mul_proj_le {m d : ℕ}
  (T : Matrix (Fin m) (Fin d) ℂ) (P : Matrix (Fin d) (Fin d) ℂ) (Q : Matrix (Fin m) (Fin m) ℂ)
  (hTP : T * P = Q * T) :
  Module.finrank ℂ (LinearMap.range (mulVecLin (T * P))) ≤
   min (Module.finrank ℂ (LinearMap.range (mulVecLin P)))
    (Module.finrank ℂ (LinearMap.range (mulVecLin Q))) := by
 refine le_min ?_ ?_
 ·
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _
 ·
  rw [hTP]
  refine Submodule.finrank_mono ?_
  rintro _ ⟨v, rfl⟩
  exact ⟨T.mulVec v, by rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]⟩
lemma finrank_range_le_sum_proj {m d k : ℕ}
  (T : Matrix (Fin m) (Fin d) ℂ) (P : Fin k → Matrix (Fin d) (Fin d) ℂ)
  (hsum : ∑ i : Fin k, P i = 1) :
  Module.finrank ℂ (LinearMap.range (mulVecLin T)) ≤
   ∑ i : Fin k, Module.finrank ℂ (LinearMap.range (mulVecLin (T * P i))) := by
 have hle : LinearMap.range (mulVecLin T) ≤
   ⨆ i : Fin k, LinearMap.range (mulVecLin (T * P i)) := by
  rintro _ ⟨v, rfl⟩
  have hv : mulVecLin T v = ∑ i : Fin k, mulVecLin (T * P i) v := by
   have h1 : T = ∑ i : Fin k, T * P i := by rw [← Matrix.mul_sum, hsum, mm1]
   conv_lhs => rw [h1]
   simp [map_sum]
  rw [hv]
  exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨v, rfl⟩
 refine (Submodule.finrank_mono hle).trans ?_
 have hgen : ∀ (s : Finset (Fin k)) (f : Fin k → Submodule ℂ (Fin m → ℂ)),
   Module.finrank ℂ (⨆ i ∈ s, f i : Submodule ℂ (Fin m → ℂ)) ≤
    ∑ i ∈ s, Module.finrank ℂ (f i) := by
  classical
  intro s f
  induction s using induction_on with
  | empty => simp
  | insert a s ha ih =>
   rw [sum_insert ha]
   have hsup_eq : (⨆ i ∈ insert a s, f i) = f a ⊔ ⨆ i ∈ s, f i := by
    simp only [Finset.mem_insert, iSup_or, iSup_sup_eq, iSup_iSup_eq_left]
   rw [hsup_eq]
   have hsup := Submodule.finrank_sup_add_finrank_inf_eq (f a) (⨆ i ∈ s, f i)
   omega
 have htop : (⨆ i : Fin k, LinearMap.range (mulVecLin (T * P i))) =
   ⨆ i ∈ (univ : Finset (Fin k)), LinearMap.range (mulVecLin (T * P i)) := by simp
 rw [htop]
 exact hgen univ (fun i => LinearMap.range (mulVecLin (T * P i)))
lemma exists_ker_proj {m d : ℕ} (T : Matrix (Fin m) (Fin d) ℂ) :
  ∃ P : Matrix (Fin d) (Fin d) ℂ,
   P.IsHermitian ∧ P * P = P ∧ T * P = 0 ∧
   ((P.trace).re : ℝ) = Module.finrank ℂ (LinearMap.ker (mulVecLin T)) := by
 let e : EuclideanSpace ℂ (Fin d) ≃ₗ[ℂ] (Fin d → ℂ) := WithLp.linearEquiv 2 ℂ (Fin d → ℂ)
 let K : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
  (LinearMap.ker (mulVecLin T)).comap e.toLinearMap
 have hdim : Module.finrank ℂ K = Module.finrank ℂ (LinearMap.ker (mulVecLin T)) := by
  have hmap : Submodule.map e.toLinearMap K = LinearMap.ker (mulVecLin T) :=
   Submodule.map_comap_eq_self (by rw [LinearEquiv.range]; exact le_top)
  rw [← hmap, LinearEquiv.finrank_map_eq]
 let b : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ K := stdOrthonormalBasis ℂ K
 let P : Matrix (Fin d) (Fin d) ℂ :=
  fun x y => ∑ k : Fin (Module.finrank ℂ K), (b k).1.ofLp x * star ((b k).1.ofLp y)
 have hPh : P.IsHermitian := by
  ext x y
  rw [ctA]
  dsimp only [P]
  rw [star_sum]
  refine sum_congr rfl fun k _ => by rw [star_mul', star_star, mul_comm]
 have hact : ∀ v : EuclideanSpace ℂ (Fin d),
   CLM P v = ∑ k, ⟪(b k).1, v⟫_ℂ • (b k).1 := by
  intro v
  apply WithLp.ofLp_injective; ext x
  dsimp only [CLM]
  rw [ofLp_toEuclideanCLM, mulVec, dotProduct]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  dsimp only [P]
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [inner_eq_star_dotProduct, dotProduct, Finset.sum_mul]
  refine sum_congr rfl fun y _ => by simp only [Pi.star_apply]; ring
 have hPp : P * P = P := by
  apply (toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).injective
  apply ContinuousLinearMap.ext
  intro v
  change CLM (P * P) v = CLM P v
  have hcomp : CLM (P * P) v = CLM P (CLM P v) := by
   dsimp only [CLM]; rw [map_mul]; rfl
  rw [hcomp, hact, hact]
  simp only [inner_sum, inner_smul_right]
  have horth : ∀ k l, ⟪(b k).1, (b l).1⟫_ℂ = if k = l then 1 else 0 :=
   fun k l => (orthonormal_iff_ite.mp b.orthonormal) k l
  simp only [horth, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
 have hTP : T * P = 0 := by
  ext i j
  rw [mul_apply, Matrix.zero_apply]
  have hcol : (fun x => P x j) = (CLM P (EuclideanSpace.single j (1 : ℂ))).ofLp := by
   ext x
   dsimp only [CLM]
   rw [ofLp_toEuclideanCLM, mulVec, dotProduct, sum_eq_single j]
   · simp
   · intro y _ hyj; simp [hyj]
   · intro h; exact absurd (mem_univ j) h
  have hmem : CLM P (EuclideanSpace.single j (1 : ℂ)) ∈ K := by
   rw [hact]
   exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (b k).2
  have hker : mulVecLin T (CLM P (EuclideanSpace.single j (1 : ℂ))).ofLp = 0 :=
   LinearMap.mem_ker.mp hmem
  have hi := congrFun hker i
  simpa [Matrix.mulVecLin_apply, mulVec, dotProduct, ← hcol] using hi
 have htr : P.trace = (Module.finrank ℂ K : ℂ) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  dsimp only [P]
  rw [sum_comm]
  have hunit : ∀ k : Fin (Module.finrank ℂ K),
    ∑ x : Fin d, (b k).1.ofLp x * star ((b k).1.ofLp x) = 1 := by
   intro k
   have h1 : ∑ x : Fin d, (b k).1.ofLp x * star ((b k).1.ofLp x) = ⟪(b k).1, (b k).1⟫_ℂ := by
    rw [inner_eq_star_dotProduct, dotProduct]
    refine sum_congr rfl fun x _ => by simp [Pi.star_apply]
   rw [h1]
   exact (orthonormal_iff_ite.mp b.orthonormal) k k |>.trans (by simp)
  simp_rw [hunit]
  simp
 refine ⟨P, hPh, hPp, hTP, ?_⟩
 rw [htr, hdim]
 simp
lemma opNorm_submatrix_cast {k l : ℕ} (h : k = l) (A : Matrix (Fin l) (Fin l) ℂ) :
  ‖CLM (Matrix.submatrix A (Fin.cast h) (Fin.cast h))‖ = ‖CLM A‖ := by
 subst h; rfl
lemma blockDecomp_of_hom_A {d m : ℕ}
  {B : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} (bdB : BDec B)
  (πB : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin m) (Fin m) ℂ)
  (h1 : πB 1 = 1)
  (hadd : ∀ x y, πB (x + y) = πB x + πB y)
  (hsmul : ∀ (c : ℂ) x, πB (c • x) = c • πB x)
  (hmul : ∀ x y, x ∈ B → y ∈ B → πB (x * y) = πB x * πB y)
  (hstar : ∀ x, πB xᴴ = (πB x)ᴴ) :
  ∃ (Bhat : StarSubalgebra ℂ (Matrix (Fin m) (Fin m) ℂ))
   (q' : Fin bdB.t → ℕ)
   (bdBhat : BDec Bhat)
   (eB : Fin bdBhat.t ≃ {i : Fin bdB.t // 0 < q' i}),
   (∀ bhat, bhat ∈ Bhat ↔ ∃ b ∈ B, πB b = bhat) ∧
   (∀ i', bdBhat.r i' = bdB.r (eB i').1) ∧
   (∀ i', bdBhat.s i' = q' (eB i').1) ∧
   (∀ i', cPr bdBhat i' = πB (cPr bdB (eB i').1)) ∧
   (∀ i, (πB (cPr bdB i)).trace = ((bdB.r i * q' i : ℕ) : ℂ)) ∧
   (∀ i, q' i = 0 → πB (cPr bdB i) = 0) ∧
   (∀ bhat ∈ Bhat, ∃ b ∈ B, ‖CLM b‖ ≤ ‖CLM bhat‖ ∧ πB b = bhat) := by
 classical
 have hzero : πB 0 = 0 := by
  have := hsmul 0 0; simpa using this
 have hsum : ∀ {α : Type} (s : Finset α) (f : α → Matrix (Fin d) (Fin d) ℂ),
   πB (∑ a ∈ s, f a) = ∑ a ∈ s, πB (f a) := by
  intro α s f
  induction s using induction_on with
  | empty => simp [hzero]
  | insert a s ha ih => rw [sum_insert ha, hadd, ih, sum_insert ha]
 let Bhat : StarSubalgebra ℂ (Matrix (Fin m) (Fin m) ℂ) :=
  {
   carrier := {y | ∃ b ∈ B, πB b = y}
   mul_mem' := by rintro _ _ ⟨b₁, hb₁, rfl⟩ ⟨b₂, hb₂, rfl⟩; exact ⟨b₁ * b₂, B.mul_mem hb₁ hb₂, hmul _ _ hb₁ hb₂⟩
   one_mem' := ⟨1, B.one_mem, h1⟩
   add_mem' := by rintro _ _ ⟨b₁, hb₁, rfl⟩ ⟨b₂, hb₂, rfl⟩; exact ⟨b₁ + b₂, B.add_mem hb₁ hb₂, hadd _ _⟩
   zero_mem' := ⟨0, B.zero_mem, hzero⟩
   algebraMap_mem' := fun c => ⟨algebraMap ℂ _ c, B.algebraMap_mem c, by
    simp only [Algebra.algebraMap_eq_smul_one, hsmul, h1]⟩
   star_mem' := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨bᴴ, star_mem hb, hstar b⟩ }
 let eA (i : Fin bdB.t) (a c : Fin (bdB.r i)) : Matrix (Fin m) (Fin m) ℂ :=
  πB (mUA bdB i a c)
 have heA_star : ∀ i a c, (eA i a c)ᴴ = eA i c a := fun i a c => by
  simp only [eA, ← hstar, matUnitA_conjTranspose]
 have heA_mul_same : ∀ i a b c d, eA i a b * eA i c d = if b = c then eA i a d else 0 := by
  intro i a b c d
  simp only [eA, ← hmul _ _ (mUA_mem bdB i a b) (mUA_mem bdB i c d), mUA_mul]
  split_ifs <;> simp [hzero]
 have heA_mul_ne : ∀ {i j}, i ≠ j → ∀ a b c d, eA i a b * eA j c d = 0 := by
  intro i j hij a b c d
  simp only [eA, ← hmul _ _ (mUA_mem bdB i a b) (mUA_mem bdB j c d),
   matUnitA_mul_ne bdB hij, hzero]
 have heA_proj_h : ∀ i a, (eA i a a).IsHermitian := fun i a => heA_star i a a
 have heA_proj_p : ∀ i a, eA i a a * eA i a a = eA i a a := fun i a => by
  simpa using heA_mul_same i a a a a
 let q' : Fin bdB.t → ℕ := fun i =>
  Module.finrank ℂ (LinearMap.range (CLM (eA i ⟨0, bdB.hr i⟩ ⟨0, bdB.hr i⟩)).toLinearMap)
 have htr_eA : ∀ i a, (eA i a a).trace = (q' i : ℂ) := by
  intro i a
  have htr0 : (eA i ⟨0, bdB.hr i⟩ ⟨0, bdB.hr i⟩).trace = (q' i : ℂ) :=
   proj_trace_eq_finrank_range (heA_proj_h i _) (heA_proj_p i _)
  calc
   (eA i a a).trace = (eA i a ⟨0, bdB.hr i⟩ * eA i ⟨0, bdB.hr i⟩ a).trace := by
      rw [heA_mul_same]; simp
   _ = (eA i ⟨0, bdB.hr i⟩ a * eA i a ⟨0, bdB.hr i⟩).trace := trace_mul_comm _ _
   _ = (eA i ⟨0, bdB.hr i⟩ ⟨0, bdB.hr i⟩).trace := by rw [heA_mul_same]; simp
   _ = (q' i : ℂ) := htr0
 have htr_w : ∀ i, (πB (cPr bdB i)).trace = ((bdB.r i * q' i : ℕ) : ℂ) := by
  intro i
  rw [← sum_matUnitA_diag bdB i, hsum, trace_sum]
  simp only [show ∀ a, πB (mUA bdB i a a) = eA i a a from fun _ => rfl, htr_eA,
   sum_const, card_univ, card_fin, nsmul_eq_mul, Nat.cast_mul]
 have hzero_w : ∀ i, q' i = 0 → πB (cPr bdB i) = 0 := by
  intro i hq0
  have hPh : (πB (cPr bdB i)).IsHermitian := by
   dsimp only [IsHermitian]; rw [← hstar, cPr_herm]
  have hPp : πB (cPr bdB i) * πB (cPr bdB i) = πB (cPr bdB i) := by
   rw [← hmul _ _ (cPr_mem bdB i) (cPr_mem bdB i), cPr_mul]; simp
  apply proj_eq_zero_of_trace_re_zero hPh hPp
  rw [htr_w i, hq0]; simp
 let I' := {i : Fin bdB.t // 0 < q' i}
 let t' := Fintype.card I'
 let eB : Fin t' ≃ I' := (Fintype.equivFin I').symm
 let r' : Fin t' → ℕ := fun i' => bdB.r (eB i').1
 let s' : Fin t' → ℕ := fun i' => q' (eB i').1
 let V0 (i' : Fin t') : Submodule ℂ (EuclideanSpace ℂ (Fin m)) :=
  LinearMap.range (CLM (eA (eB i').1 ⟨0, bdB.hr _⟩ ⟨0, bdB.hr _⟩)).toLinearMap
 let eb0 (i' : Fin t') : OrthonormalBasis (Fin (s' i')) ℂ (V0 i') :=
  stdOrthonormalBasis ℂ (V0 i')
 have heb0_fix : ∀ i' k, CLM (eA (eB i').1 ⟨0, bdB.hr _⟩ ⟨0, bdB.hr _⟩) (eb0 i' k).1 = (eb0 i' k).1 := by
  intro i' k
  rcases (eb0 i' k).2 with ⟨v, hv⟩
  have hv' : CLM (eA (eB i').1 ⟨0, bdB.hr _⟩ ⟨0, bdB.hr _⟩) v = (eb0 i' k).1 := hv
  rw [← hv']
  have hcomp : CLM (eA (eB i').1 ⟨0, bdB.hr _⟩ ⟨0, bdB.hr _⟩)
    (CLM (eA (eB i').1 ⟨0, bdB.hr _⟩ ⟨0, bdB.hr _⟩) v) =
    CLM (eA (eB i').1 ⟨0, bdB.hr _⟩ ⟨0, bdB.hr _⟩ *
     eA (eB i').1 ⟨0, bdB.hr _⟩ ⟨0, bdB.hr _⟩) v := by
   dsimp only [CLM]; rw [map_mul]; rfl
  rw [hcomp, heA_proj_p]
 let bvec : (Σ i' : Fin t', Fin (r' i') × Fin (s' i')) → EuclideanSpace ℂ (Fin m) :=
  fun ⟨i', a, k⟩ => CLM (eA (eB i').1 a ⟨0, bdB.hr _⟩) (eb0 i' k).1
 have hbvec_orth : Orthonormal ℂ bvec := by
  rw [orthonormal_iff_ite]
  rintro ⟨i', a, k⟩ ⟨j', c, l⟩
  dsimp only [bvec]
  have hadj : ⟪CLM (eA (eB i').1 a ⟨0, bdB.hr _⟩) (eb0 i' k).1,
    CLM (eA (eB j').1 c ⟨0, bdB.hr _⟩) (eb0 j' l).1⟫_ℂ =
    ⟪(eb0 i' k).1, CLM (eA (eB i').1 ⟨0, bdB.hr _⟩ a *
     eA (eB j').1 c ⟨0, bdB.hr _⟩) (eb0 j' l).1⟫_ℂ := by
   have h1 : CLM (eA (eB i').1 a ⟨0, bdB.hr _⟩) =
     ContinuousLinearMap.adjoint (CLM (eA (eB i').1 ⟨0, bdB.hr _⟩ a)) := by
    rw [toCLM_adjoint, heA_star]
   conv_lhs => rw [h1]
   rw [ContinuousLinearMap.adjoint_inner_left]
   have hcomp : CLM (eA (eB i').1 ⟨0, bdB.hr _⟩ a)
     (CLM (eA (eB j').1 c ⟨0, bdB.hr _⟩) (eb0 j' l).1) =
     CLM (eA (eB i').1 ⟨0, bdB.hr _⟩ a * eA (eB j').1 c ⟨0, bdB.hr _⟩) (eb0 j' l).1 := by
    dsimp only [CLM]; rw [map_mul]; rfl
   rw [hcomp]
  rw [hadj]
  by_cases hij : i' = j'
  ·
   subst hij
   rw [heA_mul_same]
   by_cases hac : a = c
   ·
    subst hac
    simp only [↓reduceIte, heb0_fix]
    have horth : ⟪(eb0 i' k).1, (eb0 i' l).1⟫_ℂ = if k = l then 1 else 0 :=
     (orthonormal_iff_ite.mp (eb0 i').orthonormal) k l
    rw [horth]
    by_cases hkl : k = l <;> simp [hkl]
   ·
    simp only [if_neg hac]
    have h0 : CLM (0 : Matrix (Fin m) (Fin m) ℂ) (eb0 i' l).1 = 0 := by
     dsimp only [CLM]; rw [map_zero]; rfl
    rw [h0, inner_zero_right]
    have hne : (⟨i', a, k⟩ : Σ i' : Fin t', Fin (r' i') × Fin (s' i')) ≠ ⟨i', c, l⟩ := by
     intro h; cases h; exact hac rfl
    rw [if_neg hne]
  ·
   have hij' : (eB i').1 ≠ (eB j').1 := fun h => hij (eB.injective (Subtype.ext h))
   rw [heA_mul_ne hij']
   have h0 : CLM (0 : Matrix (Fin m) (Fin m) ℂ) (eb0 j' l).1 = 0 := by
    dsimp only [CLM]; rw [map_zero]; rfl
   rw [h0, inner_zero_right]
   have hne : (⟨i', a, k⟩ : Σ i' : Fin t', Fin (r' i') × Fin (s' i')) ≠ ⟨j', c, l⟩ := by
    intro h; cases h; exact hij rfl
   rw [if_neg hne]
 have hcard_eq : Fintype.card (Σ i' : Fin t', Fin (r' i') × Fin (s' i')) = m := by
  have h1 : (∑ i : Fin bdB.t, (bdB.r i * q' i : ℕ) : ℂ) = (m : ℂ) := by
   have hsum1 : ∑ i : Fin bdB.t, (πB (cPr bdB i)).trace = (1 : Matrix (Fin m) (Fin m) ℂ).trace := by
    rw [← trace_sum, ← hsum, sum_cPr, h1]
   simp only [htr_w, trace_one, card_fin] at hsum1
   simpa [Nat.cast_sum] using hsum1
  have h2 : ∑ i : Fin bdB.t, bdB.r i * q' i = m := by exact_mod_cast h1
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, card_fin, r', s']
  rw [← h2]
  have hfilt : ∑ i : Fin bdB.t, bdB.r i * q' i =
    ∑ i ∈ univ.filter (fun i : Fin bdB.t => 0 < q' i), bdB.r i * q' i := by
   rw [← sum_filter_add_sum_filter_not univ (fun i : Fin bdB.t => 0 < q' i)]
   have hrest : ∑ i ∈ univ.filter (fun i : Fin bdB.t => ¬ 0 < q' i), bdB.r i * q' i = 0 := by
    refine sum_eq_zero fun i hi => ?_
    have : q' i = 0 := Nat.eq_zero_of_not_pos (mem_filter.mp hi).2
    simp [this]
   rw [hrest, add_zero]
  rw [hfilt, ← sum_attach (univ.filter fun i : Fin bdB.t => 0 < q' i)]
  let eI : I' ≃ {i // i ∈ univ.filter (fun i : Fin bdB.t => 0 < q' i)} :=
   {
    toFun := fun ⟨i, hi⟩ => ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
    invFun := fun ⟨i, hi⟩ => ⟨i, (mem_filter.mp hi).2⟩
    left_inv := fun ⟨_, _⟩ => rfl
    right_inv := fun ⟨_, _⟩ => rfl }
  exact Fintype.sum_bijective (eB.trans eI) (eB.trans eI).bijective _ _ fun _ => rfl
 let U : Matrix (Fin m) (Σ i' : Fin t', Fin (r' i') × Fin (s' i')) ℂ :=
  fun x p => (bvec p).ofLp x
 have hU_star_mul : Uᴴ * U = 1 := by
  ext p q
  rw [mul_apply, Matrix.one_apply]
  have h1 : ∑ x : Fin m, (Uᴴ) p x * U x q = ⟪bvec p, bvec q⟫_ℂ := by
   rw [inner_eq_star_dotProduct, dotProduct]
   refine sum_congr rfl fun x _ => ?_
   rw [ctA, Pi.star_apply, mul_comm]
  rw [h1, (orthonormal_iff_ite.mp hbvec_orth) p q]
 have hU_mul_star : U * Uᴴ = 1 := by
  let eIdx : (Σ i' : Fin t', Fin (r' i') × Fin (s' i')) ≃ Fin m :=
   Fintype.equivFinOfCardEq hcard_eq
  let Usq : Matrix (Fin m) (Fin m) ℂ := Matrix.submatrix U id eIdx.symm
  have hUsq : Usqᴴ * Usq = 1 := by
   ext x y
   rw [mul_apply, Matrix.one_apply]
   have := congrFun (congrFun hU_star_mul (eIdx.symm x)) (eIdx.symm y)
   rw [mul_apply, Matrix.one_apply] at this
   simpa [Usq, ctA, Matrix.submatrix_apply, eIdx.symm.injective.eq_iff] using this
  have hUsq' : Usq * Usqᴴ = 1 :=
   mul_star_self_of_mem (Matrix.mem_unitaryGroup_iff'.mpr hUsq)
  ext x y
  have := congrFun (congrFun hUsq' x) y
  rw [mul_apply] at this ⊢
  rw [← this]
  exact (Fintype.sum_bijective eIdx.symm eIdx.symm.bijective _ _ fun _ => rfl).symm
 have hconj_entry : ∀ (X : Matrix (Fin m) (Fin m) ℂ) p q,
   (Uᴴ * X * U) p q = ⟪bvec p, CLM X (bvec q)⟫_ℂ := by
  intro X p q
  rw [inner_eq_star_dotProduct, dotProduct, mul_apply]
  have hL : ∑ y, (Uᴴ * X) p y * U y q = ∑ y, ∑ x, (Uᴴ) p x * X x y * U y q := by
   refine sum_congr rfl fun y _ => by rw [mul_apply, Finset.sum_mul]
  have hR : ∑ x, (CLM X (bvec q)).ofLp x * star (bvec p).ofLp x =
    ∑ x, ∑ y, X x y * (bvec q).ofLp y * star ((bvec p).ofLp x) := by
   refine sum_congr rfl fun x _ => by
    rw [ofLp_toEuclideanCLM, mulVec, dotProduct, Finset.sum_mul]
    simp only [Pi.star_apply]
  rw [hL, hR, sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [ctA]; dsimp only [U]; ring
 have hπB_diag : ∀ (M : (i : Fin bdB.t) → Matrix (Fin (bdB.r i)) (Fin (bdB.r i)) ℂ)
   {b : Matrix (Fin d) (Fin d) ℂ},
   bdB.Uᴴ * b * bdB.U = bDA bdB.r bdB.s M →
   Uᴴ * πB b * U = bDA r' s' (fun i' => M (eB i').1) := by
  intro M b hMb
  have hb_mem : b ∈ B := (bdB.mem_iff b).mpr ⟨M, hMb⟩
  obtain ⟨M', hM', hb_exp⟩ := expand_in_matUnitA bdB hb_mem
  have hMeq : M' = M := by
   funext i a c
   have h := congrFun (congrFun (hM'.symm.trans hMb) ⟨i, a, ⟨0, bdB.hs i⟩⟩) ⟨i, c, ⟨0, bdB.hs i⟩⟩
   simpa [bDA] using h
  rw [hMeq] at hb_exp
  have hπb : πB b = ∑ i : Fin bdB.t, ∑ x : Fin (bdB.r i), ∑ y : Fin (bdB.r i),
    M i x y • eA i x y := by
   conv_lhs => rw [hb_exp]
   simp_rw [hsum, hsmul]; rfl
  ext ⟨i', a, k⟩ ⟨j', c, l⟩
  rw [hconj_entry, hπb]
  have hact_sum : CLM (∑ i : Fin bdB.t, ∑ x : Fin (bdB.r i), ∑ y : Fin (bdB.r i),
     M i x y • eA i x y) (bvec ⟨j', c, l⟩) =
    ∑ x : Fin (bdB.r (eB j').1), M (eB j').1 x c • bvec ⟨j', x, l⟩ := by
   dsimp only [CLM]
   simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply]
   rw [sum_eq_single (eB j').1]
   ·
    rw [sum_congr rfl fun x _ => ?_]
    rw [sum_eq_single c]
    ·
     congr 1
     dsimp only [bvec]
     have hcomp : CLM (eA (eB j').1 x c) (CLM (eA (eB j').1 c ⟨0, bdB.hr _⟩) (eb0 j' l).1) =
       CLM (eA (eB j').1 x c * eA (eB j').1 c ⟨0, bdB.hr _⟩) (eb0 j' l).1 := by
      dsimp only [CLM]; rw [map_mul]; rfl
     change CLM (eA (eB j').1 x c) (CLM (eA (eB j').1 c ⟨0, bdB.hr _⟩) (eb0 j' l).1) = _
     rw [hcomp, heA_mul_same]; simp
    ·
     intro y _ hyc
     dsimp only [bvec]
     have hcomp : CLM (eA (eB j').1 x y) (CLM (eA (eB j').1 c ⟨0, bdB.hr _⟩) (eb0 j' l).1) =
       CLM (eA (eB j').1 x y * eA (eB j').1 c ⟨0, bdB.hr _⟩) (eb0 j' l).1 := by
      dsimp only [CLM]; rw [map_mul]; rfl
     change M _ x y • CLM (eA _ x y) (CLM (eA _ c _) (eb0 j' l).1) = 0
     rw [hcomp, heA_mul_same, if_neg hyc]
     have h0 : CLM (0 : Matrix (Fin m) (Fin m) ℂ) (eb0 j' l).1 = 0 := by
      dsimp only [CLM]; rw [map_zero]; rfl
     rw [h0, smul_zero]
    · intro h; exact absurd (mem_univ c) h
   ·
    intro i _ hij
    refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
    dsimp only [bvec]
    have hcomp : CLM (eA i x y) (CLM (eA (eB j').1 c ⟨0, bdB.hr _⟩) (eb0 j' l).1) =
      CLM (eA i x y * eA (eB j').1 c ⟨0, bdB.hr _⟩) (eb0 j' l).1 := by
     dsimp only [CLM]; rw [map_mul]; rfl
    change M i x y • CLM (eA i x y) (CLM (eA _ c _) (eb0 j' l).1) = 0
    rw [hcomp, heA_mul_ne hij]
    have h0 : CLM (0 : Matrix (Fin m) (Fin m) ℂ) (eb0 j' l).1 = 0 := by
     dsimp only [CLM]; rw [map_zero]; rfl
    rw [h0, smul_zero]
   · intro h; exact absurd (mem_univ _) h
  rw [hact_sum, inner_sum]
  simp_rw [inner_smul_right, orthonormal_iff_ite.mp hbvec_orth]
  by_cases hij : i' = j'
  ·
   subst hij
   simp only [bDA, ↓reduceDIte]
   by_cases hkl : k = l
   ·
    subst hkl
    simp only [↓reduceIte]
    rw [sum_eq_single a]
    · simp
    ·
     intro x _ hxa
     have hne : (⟨i', a, k⟩ : Σ i' : Fin t', Fin (r' i') × Fin (s' i')) ≠ ⟨i', x, k⟩ := by
      intro h; cases h; exact hxa rfl
     simp [hne]
    · intro h; exact absurd (mem_univ a) h
   ·
    simp only [if_neg hkl]
    refine sum_eq_zero fun x _ => ?_
    have hne : (⟨i', a, k⟩ : Σ i' : Fin t', Fin (r' i') × Fin (s' i')) ≠ ⟨i', x, l⟩ := by
     intro h; cases h; exact hkl rfl
    simp [hne]
  ·
   simp only [bDA, dif_neg hij]
   refine sum_eq_zero fun x _ => ?_
   have hne : (⟨i', a, k⟩ : Σ i' : Fin t', Fin (r' i') × Fin (s' i')) ≠ ⟨j', x, l⟩ := by
    intro h; cases h; exact hij rfl
   simp [hne]
 let bdBhat : BDec Bhat :=
  {
   t := t'
   r := r'
   s := s'
   hr := fun i' => bdB.hr (eB i').1
   hs := fun i' => (eB i').2
   U := U
   U_star_mul := hU_star_mul
   U_mul_star := hU_mul_star
   mem_iff := fun y => by
    constructor
    ·
     rintro ⟨b, hb, rfl⟩
     obtain ⟨M, hM⟩ := (bdB.mem_iff b).mp hb
     exact ⟨fun i' => M (eB i').1, hπB_diag M hM⟩
    ·
     rintro ⟨M', hM'⟩
     let M : (i : Fin bdB.t) → Matrix (Fin (bdB.r i)) (Fin (bdB.r i)) ℂ := fun i =>
      if h : 0 < q' i then
       Matrix.submatrix (M' (eB.symm ⟨i, h⟩))
        (Fin.cast (congrArg (fun x : I' => bdB.r x.1) (eB.apply_symm_apply ⟨i, h⟩)).symm)
        (Fin.cast (congrArg (fun x : I' => bdB.r x.1) (eB.apply_symm_apply ⟨i, h⟩)).symm)
      else 0
     let b : Matrix (Fin d) (Fin d) ℂ := bdB.U * bDA bdB.r bdB.s M * bdB.Uᴴ
     have hMb : bdB.Uᴴ * b * bdB.U = bDA bdB.r bdB.s M := by
      simp only [b]
      calc
       bdB.Uᴴ * (bdB.U * bDA bdB.r bdB.s M * bdB.Uᴴ) * bdB.U
        = (bdB.Uᴴ * bdB.U) * bDA bdB.r bdB.s M * (bdB.Uᴴ * bdB.U) := by
          simp only [mma]
       _ = bDA bdB.r bdB.s M := by rw [bdB.U_star_mul, m1m, mm1]
     have hb_mem : b ∈ B := (bdB.mem_iff b).mpr ⟨M, hMb⟩
     have hMeq : (fun i' => M (eB i').1) = M' := by
      funext i'
      have hpos : 0 < q' (eB i').1 := (eB i').2
      have hsymm : eB.symm ⟨(eB i').1, hpos⟩ = i' := eB.symm_apply_apply i'
      dsimp only [M]
      rw [dif_pos hpos]
      ext a c
      rw [Matrix.submatrix_apply]
      generalize_proofs h1
      revert h1
      rw [hsymm]
      intro h1
      rfl
     have hdiag := hπB_diag M hMb
     rw [hMeq] at hdiag
     refine ⟨b, hb_mem, ?_⟩
     calc
      πB b = U * (Uᴴ * πB b * U) * Uᴴ := by
         calc
          πB b = (U * Uᴴ) * πB b * (U * Uᴴ) := by rw [hU_mul_star, m1m, mm1]
          _ = U * (Uᴴ * πB b * U) * Uᴴ := by simp only [mma]
      _ = U * (Uᴴ * y * U) * Uᴴ := by rw [hdiag, hM']
      _ = y := by
         calc
          U * (Uᴴ * y * U) * Uᴴ = (U * Uᴴ) * y * (U * Uᴴ) := by simp only [mma]
          _ = y := by rw [hU_mul_star, m1m, mm1] }
 refine ⟨Bhat, q', bdBhat, eB, fun _ => Iff.rfl, fun _ => rfl, fun _ => rfl, ?_, htr_w, hzero_w, ?_⟩
 ·
  intro i'
  have hdiag := hπB_diag (fun k => if k = (eB i').1 then 1 else 0) (centralProj_conj bdB (eB i').1)
  have hfn : (fun k' : Fin t' => if (eB k').1 = (eB i').1 then
    (1 : Matrix (Fin (r' k')) (Fin (r' k')) ℂ) else 0) =
    fun k' => if k' = i' then 1 else 0 := by
   funext k'
   by_cases h : k' = i'
   · subst h; simp
   ·
    have hne : (eB k').1 ≠ (eB i').1 := fun heq => h (eB.injective (Subtype.ext heq))
    simp [h, hne]
  rw [hfn] at hdiag
  change U * bDA r' s' (fun k' => if k' = i' then 1 else 0) * Uᴴ = πB (cPr bdB (eB i').1)
  rw [← hdiag]
  calc
   U * (Uᴴ * πB (cPr bdB (eB i').1) * U) * Uᴴ
    = (U * Uᴴ) * πB (cPr bdB (eB i').1) * (U * Uᴴ) := by simp only [mma]
   _ = πB (cPr bdB (eB i').1) := by rw [hU_mul_star, m1m, mm1]
 ·
  intro y hy
  obtain ⟨M', hM'⟩ := (bdBhat.mem_iff y).mp hy
  let M : (i : Fin bdB.t) → Matrix (Fin (bdB.r i)) (Fin (bdB.r i)) ℂ := fun i =>
   if h : 0 < q' i then
    Matrix.submatrix (M' (eB.symm ⟨i, h⟩))
     (Fin.cast (congrArg (fun x : I' => bdB.r x.1) (eB.apply_symm_apply ⟨i, h⟩)).symm)
     (Fin.cast (congrArg (fun x : I' => bdB.r x.1) (eB.apply_symm_apply ⟨i, h⟩)).symm)
   else 0
  let b : Matrix (Fin d) (Fin d) ℂ := bdB.U * bDA bdB.r bdB.s M * bdB.Uᴴ
  have hMb : bdB.Uᴴ * b * bdB.U = bDA bdB.r bdB.s M := by
   simp only [b]
   calc
    bdB.Uᴴ * (bdB.U * bDA bdB.r bdB.s M * bdB.Uᴴ) * bdB.U
     = (bdB.Uᴴ * bdB.U) * bDA bdB.r bdB.s M * (bdB.Uᴴ * bdB.U) := by simp only [mma]
    _ = bDA bdB.r bdB.s M := by rw [bdB.U_star_mul, m1m, mm1]
  have hb_mem : b ∈ B := (bdB.mem_iff b).mpr ⟨M, hMb⟩
  have hMeq : (fun i' => M (eB i').1) = M' := by
   funext i'
   have hpos : 0 < q' (eB i').1 := (eB i').2
   have hsymm : eB.symm ⟨(eB i').1, hpos⟩ = i' := eB.symm_apply_apply i'
   dsimp only [M]
   rw [dif_pos hpos]
   ext a c
   rw [Matrix.submatrix_apply]
   generalize_proofs h1
   revert h1
   rw [hsymm]
   intro h1
   rfl
  have hπb : πB b = y := by
   have hdiag := hπB_diag M hMb
   rw [hMeq] at hdiag
   calc
    πB b = U * (Uᴴ * πB b * U) * Uᴴ := by
       calc
        πB b = (U * Uᴴ) * πB b * (U * Uᴴ) := by rw [hU_mul_star, m1m, mm1]
        _ = U * (Uᴴ * πB b * U) * Uᴴ := by simp only [mma]
    _ = U * (Uᴴ * y * U) * Uᴴ := by rw [hdiag, hM']
    _ = y := by
       calc
        U * (Uᴴ * y * U) * Uᴴ = (U * Uᴴ) * y * (U * Uᴴ) := by simp only [mma]
        _ = y := by rw [hU_mul_star, m1m, mm1]
  have hop_le : ‖CLM b‖ ≤ ‖CLM y‖ := by
   have h1 : ‖CLM b‖ ≤ ‖CLM (bDA bdB.r bdB.s M)‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    have hbU : ‖CLM b‖ ≤ ‖CLM (bDA bdB.r bdB.s M)‖ := by
     have hP : (bdB.Uᴴ * bdB.U) * (bdB.Uᴴ * bdB.U) = bdB.Uᴴ * bdB.U := by
      rw [bdB.U_star_mul, m1m]
     exact opN_conjPI bdB.U hP (bDA bdB.r bdB.s M)
    exact ((CLM b).le_opNorm v).trans (mul_le_mul_of_nonneg_right hbU (norm_nonneg v))
   have h2 : ‖CLM (bDA bdB.r bdB.s M)‖ ≤ ‖CLM (bDA r' s' M')‖ := by
    refine opNorm_blockDiagA_le M (norm_nonneg _) fun i => ?_
    dsimp only [M]
    by_cases hpos : 0 < q' i
    ·
     rw [dif_pos hpos, opNorm_submatrix_cast]
     exact opNorm_le_blockDiagA bdBhat.hs M' (eB.symm ⟨i, hpos⟩)
    ·
     rw [dif_neg hpos]
     have h0 : CLM (0 : Matrix (Fin (bdB.r i)) (Fin (bdB.r i)) ℂ) = 0 := by
      dsimp only [CLM]; exact map_zero _
     rw [h0, norm_zero]
     exact norm_nonneg _
   have h3 : ‖CLM (bDA r' s' M')‖ ≤ ‖CLM y‖ := by
    rw [← hM']
    have hP : (Uᴴᴴ * Uᴴ) * (Uᴴᴴ * Uᴴ) = Uᴴᴴ * Uᴴ := by
     rw [ctct, hU_mul_star, m1m]
    have h := opN_conjPI Uᴴ hP y
    simpa [ctct] using h
   exact h1.trans (h2.trans h3)
  exact ⟨b, hb_mem, hop_le, hπb⟩
lemma blockDecomp_of_hom_C {d m : ℕ}
  {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} (bdA : BDec A)
  (πA' : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin m) (Fin m) ℂ)
  (h1 : πA' 1 = 1)
  (hadd : ∀ c₁ c₂, c₁ ∈ comm A → c₂ ∈ comm A → πA' (c₁ + c₂) = πA' c₁ + πA' c₂)
  (hsmul : ∀ (α : ℂ) c, c ∈ comm A → πA' (α • c) = α • πA' c)
  (hmul : ∀ c₁ c₂, c₁ ∈ comm A → c₂ ∈ comm A → πA' (c₁ * c₂) = πA' c₁ * πA' c₂)
  (hstar : ∀ c, c ∈ comm A → πA' cᴴ = (πA' c)ᴴ) :
  ∃ (Ahat : StarSubalgebra ℂ (Matrix (Fin m) (Fin m) ℂ))
   (r' : Fin bdA.t → ℕ)
   (bdAhat : BDec Ahat)
   (eA : Fin bdAhat.t ≃ {j : Fin bdA.t // 0 < r' j}),
   (∀ x, x ∈ Ahat ↔ ∀ c ∈ comm A, x * πA' c = πA' c * x) ∧
   (∀ j', bdAhat.r j' = r' (eA j').1) ∧
   (∀ j', bdAhat.s j' = bdA.s (eA j').1) ∧
   (∀ j', cPr bdAhat j' = πA' (cPr bdA (eA j').1)) ∧
   (∀ j, (πA' (cPr bdA j)).trace = ((r' j * bdA.s j : ℕ) : ℂ)) ∧
   (∀ j, r' j = 0 → πA' (cPr bdA j) = 0) := by
 classical
 have hzero : πA' 0 = 0 := by
  have := hsmul 0 0 (comm A).zero_mem; simpa using this
 have hsum : ∀ {α : Type} (s : Finset α) (f : α → Matrix (Fin d) (Fin d) ℂ),
   (∀ a ∈ s, f a ∈ comm A) →
   πA' (∑ a ∈ s, f a) = ∑ a ∈ s, πA' (f a) := by
  intro α s f hf
  induction s using induction_on with
  | empty => simp [hzero]
  | insert a s ha ih =>
   rw [sum_insert ha, hadd _ _ (hf a (Finset.mem_insert_self a s))
    ((comm A).sum_mem fun x hx => hf x (Finset.mem_insert_of_mem hx)),
    ih fun x hx => hf x (Finset.mem_insert_of_mem hx), sum_insert ha]
 let Cimg : StarSubalgebra ℂ (Matrix (Fin m) (Fin m) ℂ) :=
  {
   carrier := {y | ∃ c ∈ comm A, πA' c = y}
   mul_mem' := by rintro _ _ ⟨c₁, h₁, rfl⟩ ⟨c₂, h₂, rfl⟩; exact ⟨c₁ * c₂, (comm A).mul_mem h₁ h₂, hmul _ _ h₁ h₂⟩
   one_mem' := ⟨1, (comm A).one_mem, h1⟩
   add_mem' := by rintro _ _ ⟨c₁, h₁, rfl⟩ ⟨c₂, h₂, rfl⟩; exact ⟨c₁ + c₂, (comm A).add_mem h₁ h₂, hadd _ _ h₁ h₂⟩
   zero_mem' := ⟨0, (comm A).zero_mem, hzero⟩
   algebraMap_mem' := fun α => ⟨algebraMap ℂ _ α, (comm A).algebraMap_mem α, by
    simp only [Algebra.algebraMap_eq_smul_one, hsmul _ _ (comm A).one_mem, h1]⟩
   star_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨cᴴ, star_mem hc, hstar c hc⟩ }
 let Ahat := comm Cimg
 let fC (j : Fin bdA.t) (b d' : Fin (bdA.s j)) : Matrix (Fin m) (Fin m) ℂ :=
  πA' (mUC bdA j b d')
 have hfC_star : ∀ j b d', (fC j b d')ᴴ = fC j d' b := fun j b d' => by
  simp only [fC, ← hstar _ (matUnitC_mem bdA j b d'), matUnitC_conjTranspose]
 have hfC_mul_same : ∀ j b₁ b₂ b₃ b₄, fC j b₁ b₂ * fC j b₃ b₄ = if b₂ = b₃ then fC j b₁ b₄ else 0 := by
  intro j b₁ b₂ b₃ b₄
  simp only [fC, ← hmul _ _ (matUnitC_mem bdA j b₁ b₂) (matUnitC_mem bdA j b₃ b₄), matUnitC_mul_same]
  split_ifs <;> simp [hzero]
 have hfC_mul_ne : ∀ {i j}, i ≠ j → ∀ b₁ b₂ b₃ b₄, fC i b₁ b₂ * fC j b₃ b₄ = 0 := by
  intro i j hij b₁ b₂ b₃ b₄
  simp only [fC, ← hmul _ _ (matUnitC_mem bdA i b₁ b₂) (matUnitC_mem bdA j b₃ b₄),
   matUnitC_mul_ne bdA hij, hzero]
 have hfC_proj_h : ∀ j b, (fC j b b).IsHermitian := fun j b => hfC_star j b b
 have hfC_proj_p : ∀ j b, fC j b b * fC j b b = fC j b b := fun j b => by
  simpa using hfC_mul_same j b b b b
 let r' : Fin bdA.t → ℕ := fun j =>
  Module.finrank ℂ (LinearMap.range (CLM (fC j ⟨0, bdA.hs j⟩ ⟨0, bdA.hs j⟩)).toLinearMap)
 have htr_fC : ∀ j b, (fC j b b).trace = (r' j : ℂ) := by
  intro j b
  have htr0 : (fC j ⟨0, bdA.hs j⟩ ⟨0, bdA.hs j⟩).trace = (r' j : ℂ) :=
   proj_trace_eq_finrank_range (hfC_proj_h j _) (hfC_proj_p j _)
  calc
   (fC j b b).trace = (fC j b ⟨0, bdA.hs j⟩ * fC j ⟨0, bdA.hs j⟩ b).trace := by
      rw [hfC_mul_same]; simp
   _ = (fC j ⟨0, bdA.hs j⟩ b * fC j b ⟨0, bdA.hs j⟩).trace := trace_mul_comm _ _
   _ = (fC j ⟨0, bdA.hs j⟩ ⟨0, bdA.hs j⟩).trace := by rw [hfC_mul_same]; simp
   _ = (r' j : ℂ) := htr0
 have htr_z : ∀ j, (πA' (cPr bdA j)).trace = ((r' j * bdA.s j : ℕ) : ℂ) := by
  intro j
  rw [← sum_matUnitC_diag bdA j, hsum _ _ (fun b _ => matUnitC_mem bdA j b b), trace_sum]
  simp only [show ∀ b, πA' (mUC bdA j b b) = fC j b b from fun _ => rfl, htr_fC,
   sum_const, card_univ, card_fin, nsmul_eq_mul, Nat.cast_mul, mul_comm]
 have hzero_z : ∀ j, r' j = 0 → πA' (cPr bdA j) = 0 := by
  intro j hr0
  have hPh : (πA' (cPr bdA j)).IsHermitian := by
   dsimp only [IsHermitian]
   rw [← hstar _ (cPr_comm bdA j), cPr_herm]
  have hPp : πA' (cPr bdA j) * πA' (cPr bdA j) = πA' (cPr bdA j) := by
   rw [← hmul _ _ (cPr_comm bdA j) (cPr_comm bdA j), cPr_mul]; simp
  apply proj_eq_zero_of_trace_re_zero hPh hPp
  rw [htr_z j, hr0]; simp
 let J' := {j : Fin bdA.t // 0 < r' j}
 let t' := Fintype.card J'
 let eA : Fin t' ≃ J' := (Fintype.equivFin J').symm
 let rA : Fin t' → ℕ := fun j' => r' (eA j').1
 let sA : Fin t' → ℕ := fun j' => bdA.s (eA j').1
 let W0 (j' : Fin t') : Submodule ℂ (EuclideanSpace ℂ (Fin m)) :=
  LinearMap.range (CLM (fC (eA j').1 ⟨0, bdA.hs _⟩ ⟨0, bdA.hs _⟩)).toLinearMap
 let eb0 (j' : Fin t') : OrthonormalBasis (Fin (rA j')) ℂ (W0 j') :=
  stdOrthonormalBasis ℂ (W0 j')
 have heb0_fix : ∀ j' a, CLM (fC (eA j').1 ⟨0, bdA.hs _⟩ ⟨0, bdA.hs _⟩) (eb0 j' a).1 = (eb0 j' a).1 := by
  intro j' a
  rcases (eb0 j' a).2 with ⟨v, hv⟩
  have hv' : CLM (fC (eA j').1 ⟨0, bdA.hs _⟩ ⟨0, bdA.hs _⟩) v = (eb0 j' a).1 := hv
  rw [← hv']
  have hcomp : CLM (fC (eA j').1 ⟨0, bdA.hs _⟩ ⟨0, bdA.hs _⟩)
    (CLM (fC (eA j').1 ⟨0, bdA.hs _⟩ ⟨0, bdA.hs _⟩) v) =
    CLM (fC (eA j').1 ⟨0, bdA.hs _⟩ ⟨0, bdA.hs _⟩ *
     fC (eA j').1 ⟨0, bdA.hs _⟩ ⟨0, bdA.hs _⟩) v := by
   dsimp only [CLM]; rw [map_mul]; rfl
  rw [hcomp, hfC_proj_p]
 let bvec : (Σ j' : Fin t', Fin (rA j') × Fin (sA j')) → EuclideanSpace ℂ (Fin m) :=
  fun ⟨j', a, b⟩ => CLM (fC (eA j').1 b ⟨0, bdA.hs _⟩) (eb0 j' a).1
 have hbvec_orth : Orthonormal ℂ bvec := by
  rw [orthonormal_iff_ite]
  rintro ⟨i', a, b⟩ ⟨j', c, d'⟩
  dsimp only [bvec]
  have hadj : ⟪CLM (fC (eA i').1 b ⟨0, bdA.hs _⟩) (eb0 i' a).1,
    CLM (fC (eA j').1 d' ⟨0, bdA.hs _⟩) (eb0 j' c).1⟫_ℂ =
    ⟪(eb0 i' a).1, CLM (fC (eA i').1 ⟨0, bdA.hs _⟩ b *
     fC (eA j').1 d' ⟨0, bdA.hs _⟩) (eb0 j' c).1⟫_ℂ := by
   have h1 : CLM (fC (eA i').1 b ⟨0, bdA.hs _⟩) =
     ContinuousLinearMap.adjoint (CLM (fC (eA i').1 ⟨0, bdA.hs _⟩ b)) := by
    rw [toCLM_adjoint, hfC_star]
   conv_lhs => rw [h1]
   rw [ContinuousLinearMap.adjoint_inner_left]
   have hcomp : CLM (fC (eA i').1 ⟨0, bdA.hs _⟩ b)
     (CLM (fC (eA j').1 d' ⟨0, bdA.hs _⟩) (eb0 j' c).1) =
     CLM (fC (eA i').1 ⟨0, bdA.hs _⟩ b * fC (eA j').1 d' ⟨0, bdA.hs _⟩) (eb0 j' c).1 := by
    dsimp only [CLM]; rw [map_mul]; rfl
   rw [hcomp]
  rw [hadj]
  by_cases hij : i' = j'
  ·
   subst hij
   rw [hfC_mul_same]
   by_cases hbd : b = d'
   ·
    subst hbd
    simp only [↓reduceIte, heb0_fix]
    have horth : ⟪(eb0 i' a).1, (eb0 i' c).1⟫_ℂ = if a = c then 1 else 0 :=
     (orthonormal_iff_ite.mp (eb0 i').orthonormal) a c
    rw [horth]
    by_cases hac : a = c <;> simp [hac]
   ·
    simp only [if_neg hbd]
    have h0 : CLM (0 : Matrix (Fin m) (Fin m) ℂ) (eb0 i' c).1 = 0 := by
     dsimp only [CLM]; rw [map_zero]; rfl
    rw [h0, inner_zero_right]
    have hne : (⟨i', a, b⟩ : Σ j' : Fin t', Fin (rA j') × Fin (sA j')) ≠ ⟨i', c, d'⟩ := by
     intro h; cases h; exact hbd rfl
    rw [if_neg hne]
  ·
   have hij' : (eA i').1 ≠ (eA j').1 := fun h => hij (eA.injective (Subtype.ext h))
   rw [hfC_mul_ne hij']
   have h0 : CLM (0 : Matrix (Fin m) (Fin m) ℂ) (eb0 j' c).1 = 0 := by
    dsimp only [CLM]; rw [map_zero]; rfl
   rw [h0, inner_zero_right]
   have hne : (⟨i', a, b⟩ : Σ j' : Fin t', Fin (rA j') × Fin (sA j')) ≠ ⟨j', c, d'⟩ := by
    intro h; cases h; exact hij rfl
   rw [if_neg hne]
 have hcard_eq : Fintype.card (Σ j' : Fin t', Fin (rA j') × Fin (sA j')) = m := by
  have h1 : (∑ j : Fin bdA.t, (r' j * bdA.s j : ℕ) : ℂ) = (m : ℂ) := by
   have hsum1 : ∑ j : Fin bdA.t, (πA' (cPr bdA j)).trace = (1 : Matrix (Fin m) (Fin m) ℂ).trace := by
    rw [← trace_sum, ← hsum _ _ (fun j _ => cPr_comm bdA j), sum_cPr, h1]
   simp only [htr_z, trace_one, card_fin] at hsum1
   simpa [Nat.cast_sum] using hsum1
  have h2 : ∑ j : Fin bdA.t, r' j * bdA.s j = m := by exact_mod_cast h1
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, card_fin, rA, sA]
  rw [← h2]
  have hfilt : ∑ j : Fin bdA.t, r' j * bdA.s j =
    ∑ j ∈ univ.filter (fun j : Fin bdA.t => 0 < r' j), r' j * bdA.s j := by
   rw [← sum_filter_add_sum_filter_not univ (fun j : Fin bdA.t => 0 < r' j)]
   have hrest : ∑ j ∈ univ.filter (fun j : Fin bdA.t => ¬ 0 < r' j), r' j * bdA.s j = 0 := by
    refine sum_eq_zero fun j hj => ?_
    have : r' j = 0 := Nat.eq_zero_of_not_pos (mem_filter.mp hj).2
    simp [this]
   rw [hrest, add_zero]
  rw [hfilt, ← sum_attach (univ.filter fun j : Fin bdA.t => 0 < r' j)]
  let eJ : J' ≃ {j // j ∈ univ.filter (fun j : Fin bdA.t => 0 < r' j)} :=
   {
    toFun := fun ⟨j, hj⟩ => ⟨j, mem_filter.mpr ⟨mem_univ j, hj⟩⟩
    invFun := fun ⟨j, hj⟩ => ⟨j, (mem_filter.mp hj).2⟩
    left_inv := fun ⟨_, _⟩ => rfl
    right_inv := fun ⟨_, _⟩ => rfl }
  exact Fintype.sum_bijective (eA.trans eJ) (eA.trans eJ).bijective _ _ fun _ => rfl
 let U : Matrix (Fin m) (Σ j' : Fin t', Fin (rA j') × Fin (sA j')) ℂ :=
  fun x p => (bvec p).ofLp x
 have hU_star_mul : Uᴴ * U = 1 := by
  ext p q
  rw [mul_apply, Matrix.one_apply]
  have h1 : ∑ x : Fin m, (Uᴴ) p x * U x q = ⟪bvec p, bvec q⟫_ℂ := by
   rw [inner_eq_star_dotProduct, dotProduct]
   refine sum_congr rfl fun x _ => ?_
   rw [ctA, Pi.star_apply, mul_comm]
  rw [h1, (orthonormal_iff_ite.mp hbvec_orth) p q]
 have hU_mul_star : U * Uᴴ = 1 := by
  let eIdx : (Σ j' : Fin t', Fin (rA j') × Fin (sA j')) ≃ Fin m :=
   Fintype.equivFinOfCardEq hcard_eq
  let Usq : Matrix (Fin m) (Fin m) ℂ := Matrix.submatrix U id eIdx.symm
  have hUsq : Usqᴴ * Usq = 1 := by
   ext x y
   rw [mul_apply, Matrix.one_apply]
   have := congrFun (congrFun hU_star_mul (eIdx.symm x)) (eIdx.symm y)
   rw [mul_apply, Matrix.one_apply] at this
   simpa [Usq, ctA, Matrix.submatrix_apply, eIdx.symm.injective.eq_iff] using this
  have hUsq' : Usq * Usqᴴ = 1 :=
   mul_star_self_of_mem (Matrix.mem_unitaryGroup_iff'.mpr hUsq)
  ext x y
  have := congrFun (congrFun hUsq' x) y
  rw [mul_apply] at this ⊢
  rw [← this]
  exact (Fintype.sum_bijective eIdx.symm eIdx.symm.bijective _ _ fun _ => rfl).symm
 have hconj_entry : ∀ (X : Matrix (Fin m) (Fin m) ℂ) p q,
   (Uᴴ * X * U) p q = ⟪bvec p, CLM X (bvec q)⟫_ℂ := by
  intro X p q
  rw [inner_eq_star_dotProduct, dotProduct, mul_apply]
  have hL : ∑ y, (Uᴴ * X) p y * U y q = ∑ y, ∑ x, (Uᴴ) p x * X x y * U y q := by
   refine sum_congr rfl fun y _ => by rw [mul_apply, Finset.sum_mul]
  have hR : ∑ x, (CLM X (bvec q)).ofLp x * star (bvec p).ofLp x =
    ∑ x, ∑ y, X x y * (bvec q).ofLp y * star ((bvec p).ofLp x) := by
   refine sum_congr rfl fun x _ => by
    rw [ofLp_toEuclideanCLM, mulVec, dotProduct, Finset.sum_mul]
    simp only [Pi.star_apply]
  rw [hL, hR, sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [ctA]; dsimp only [U]; ring
 have hπA'_diag : ∀ (N : (j : Fin bdA.t) → Matrix (Fin (bdA.s j)) (Fin (bdA.s j)) ℂ)
   {c : Matrix (Fin d) (Fin d) ℂ},
   bdA.Uᴴ * c * bdA.U = bDC bdA.r bdA.s N →
   Uᴴ * πA' c * U = bDC rA sA (fun j' => N (eA j').1) := by
  intro N c hNc
  have hc_mem : c ∈ comm A := (bDec_comm_iff bdA c).mpr ⟨N, hNc⟩
  obtain ⟨N', hN', hc_exp⟩ := expand_in_matUnitC bdA hc_mem
  have hNeq : N' = N := by
   funext j b₁ b₂
   have h := congrFun (congrFun (hN'.symm.trans hNc) ⟨j, ⟨0, bdA.hr j⟩, b₁⟩) ⟨j, ⟨0, bdA.hr j⟩, b₂⟩
   simpa [bDC] using h
  rw [hNeq] at hc_exp
  have hπc : πA' c = ∑ j : Fin bdA.t, ∑ b₁ : Fin (bdA.s j), ∑ b₂ : Fin (bdA.s j),
    N j b₁ b₂ • fC j b₁ b₂ := by
   conv_lhs => rw [hc_exp]
   rw [hsum]
   ·
    refine sum_congr rfl fun j _ => ?_
    rw [hsum]
    ·
     refine sum_congr rfl fun b₁ _ => ?_
     rw [hsum]
     · refine sum_congr rfl fun b₂ _ => hsmul _ _ (matUnitC_mem bdA j b₁ b₂)
     · intro b₂ _; exact (comm A).smul_mem (matUnitC_mem bdA j b₁ b₂) _
    · intro b₁ _; exact (comm A).sum_mem fun b₂ _ => (comm A).smul_mem (matUnitC_mem bdA j b₁ b₂) _
   ·
    intro j _; exact (comm A).sum_mem fun b₁ _ => (comm A).sum_mem fun b₂ _ =>
     (comm A).smul_mem (matUnitC_mem bdA j b₁ b₂) _
  ext ⟨i', a, b⟩ ⟨j', c', d'⟩
  rw [hconj_entry, hπc]
  have hact_sum : CLM (∑ j : Fin bdA.t, ∑ b₁ : Fin (bdA.s j), ∑ b₂ : Fin (bdA.s j),
     N j b₁ b₂ • fC j b₁ b₂) (bvec ⟨j', c', d'⟩) =
    ∑ b₁ : Fin (bdA.s (eA j').1), N (eA j').1 b₁ d' • bvec ⟨j', c', b₁⟩ := by
   dsimp only [CLM]
   simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply]
   rw [sum_eq_single (eA j').1]
   ·
    refine sum_congr rfl fun b₁ _ => ?_
    rw [sum_eq_single d']
    ·
     congr 1
     dsimp only [bvec]
     have hcomp : CLM (fC (eA j').1 b₁ d') (CLM (fC (eA j').1 d' ⟨0, bdA.hs _⟩) (eb0 j' c').1) =
       CLM (fC (eA j').1 b₁ d' * fC (eA j').1 d' ⟨0, bdA.hs _⟩) (eb0 j' c').1 := by
      dsimp only [CLM]; rw [map_mul]; rfl
     change CLM (fC _ b₁ d') (CLM (fC _ d' _) (eb0 j' c').1) = _
     rw [hcomp, hfC_mul_same]; simp
    ·
     intro b₂ _ hb
     dsimp only [bvec]
     have hcomp : CLM (fC (eA j').1 b₁ b₂) (CLM (fC (eA j').1 d' ⟨0, bdA.hs _⟩) (eb0 j' c').1) =
       CLM (fC (eA j').1 b₁ b₂ * fC (eA j').1 d' ⟨0, bdA.hs _⟩) (eb0 j' c').1 := by
      dsimp only [CLM]; rw [map_mul]; rfl
     change N _ b₁ b₂ • CLM (fC _ b₁ b₂) (CLM (fC _ d' _) (eb0 j' c').1) = 0
     rw [hcomp, hfC_mul_same, if_neg hb]
     have h0 : CLM (0 : Matrix (Fin m) (Fin m) ℂ) (eb0 j' c').1 = 0 := by
      dsimp only [CLM]; rw [map_zero]; rfl
     rw [h0, smul_zero]
    · intro h; exact absurd (mem_univ d') h
   ·
    intro j _ hj
    refine sum_eq_zero fun b₁ _ => sum_eq_zero fun b₂ _ => ?_
    dsimp only [bvec]
    have hcomp : CLM (fC j b₁ b₂) (CLM (fC (eA j').1 d' ⟨0, bdA.hs _⟩) (eb0 j' c').1) =
      CLM (fC j b₁ b₂ * fC (eA j').1 d' ⟨0, bdA.hs _⟩) (eb0 j' c').1 := by
     dsimp only [CLM]; rw [map_mul]; rfl
    change N j b₁ b₂ • CLM (fC j b₁ b₂) (CLM (fC _ d' _) (eb0 j' c').1) = 0
    rw [hcomp, hfC_mul_ne hj]
    have h0 : CLM (0 : Matrix (Fin m) (Fin m) ℂ) (eb0 j' c').1 = 0 := by
     dsimp only [CLM]; rw [map_zero]; rfl
    rw [h0, smul_zero]
   · intro h; exact absurd (mem_univ _) h
  rw [hact_sum, inner_sum]
  simp_rw [inner_smul_right, orthonormal_iff_ite.mp hbvec_orth]
  by_cases hij : i' = j'
  ·
   subst hij
   simp only [bDC, ↓reduceDIte]
   by_cases hac : a = c'
   ·
    subst hac
    simp only [↓reduceIte]
    rw [sum_eq_single b]
    · simp
    ·
     intro b₁ _ hbb
     have hne : (⟨i', a, b⟩ : Σ j' : Fin t', Fin (rA j') × Fin (sA j')) ≠ ⟨i', a, b₁⟩ := by
      intro h; cases h; exact hbb rfl
     simp [hne]
    · intro h; exact absurd (mem_univ b) h
   ·
    simp only [if_neg hac]
    refine sum_eq_zero fun b₁ _ => ?_
    have hne : (⟨i', a, b⟩ : Σ j' : Fin t', Fin (rA j') × Fin (sA j')) ≠ ⟨i', c', b₁⟩ := by
     intro h; cases h; exact hac rfl
    simp [hne]
  ·
   simp only [bDC, dif_neg hij]
   refine sum_eq_zero fun b₁ _ => ?_
   have hne : (⟨i', a, b⟩ : Σ j' : Fin t', Fin (rA j') × Fin (sA j')) ≠ ⟨j', c', b₁⟩ := by
    intro h; cases h; exact hij rfl
   simp [hne]
 have hCimg_iff : ∀ y, y ∈ Cimg ↔ ∃ N, Uᴴ * y * U = bDC rA sA N := by
  intro y
  constructor
  ·
   rintro ⟨c, hc, rfl⟩
   obtain ⟨N, hN⟩ := (bDec_comm_iff bdA c).mp hc
   exact ⟨fun j' => N (eA j').1, hπA'_diag N hN⟩
  ·
   rintro ⟨N', hN'⟩
   let N : (j : Fin bdA.t) → Matrix (Fin (bdA.s j)) (Fin (bdA.s j)) ℂ := fun j =>
    if h : 0 < r' j then
     Matrix.submatrix (N' (eA.symm ⟨j, h⟩))
      (Fin.cast (congrArg (fun x : J' => bdA.s x.1) (eA.apply_symm_apply ⟨j, h⟩)).symm)
      (Fin.cast (congrArg (fun x : J' => bdA.s x.1) (eA.apply_symm_apply ⟨j, h⟩)).symm)
    else 0
   let c : Matrix (Fin d) (Fin d) ℂ := bdA.U * bDC bdA.r bdA.s N * bdA.Uᴴ
   have hNc : bdA.Uᴴ * c * bdA.U = bDC bdA.r bdA.s N := by
    simp only [c]
    calc
     bdA.Uᴴ * (bdA.U * bDC bdA.r bdA.s N * bdA.Uᴴ) * bdA.U
      = (bdA.Uᴴ * bdA.U) * bDC bdA.r bdA.s N * (bdA.Uᴴ * bdA.U) := by simp only [mma]
     _ = bDC bdA.r bdA.s N := by rw [bdA.U_star_mul, m1m, mm1]
   have hc_mem : c ∈ comm A := (bDec_comm_iff bdA c).mpr ⟨N, hNc⟩
   have hNeq : (fun j' => N (eA j').1) = N' := by
    funext j'
    have hpos : 0 < r' (eA j').1 := (eA j').2
    have hsymm : eA.symm ⟨(eA j').1, hpos⟩ = j' := eA.symm_apply_apply j'
    dsimp only [N]
    rw [dif_pos hpos]
    ext b₁ b₂
    rw [Matrix.submatrix_apply]
    generalize_proofs h1
    revert h1
    rw [hsymm]
    intro h1
    rfl
   have hdiag := hπA'_diag N hNc
   rw [hNeq] at hdiag
   refine ⟨c, hc_mem, ?_⟩
   calc
    πA' c = U * (Uᴴ * πA' c * U) * Uᴴ := by
       calc
        πA' c = (U * Uᴴ) * πA' c * (U * Uᴴ) := by rw [hU_mul_star, m1m, mm1]
        _ = U * (Uᴴ * πA' c * U) * Uᴴ := by simp only [mma]
    _ = U * (Uᴴ * y * U) * Uᴴ := by rw [hdiag, hN']
    _ = y := by
       calc
        U * (Uᴴ * y * U) * Uᴴ = (U * Uᴴ) * y * (U * Uᴴ) := by simp only [mma]
        _ = y := by rw [hU_mul_star, m1m, mm1]
 let bdAhat : BDec Ahat :=
  {
   t := t'
   r := rA
   s := sA
   hr := fun j' => (eA j').2
   hs := fun j' => bdA.hs (eA j').1
   U := U
   U_star_mul := hU_star_mul
   U_mul_star := hU_mul_star
   mem_iff := fun x => by
    rw [mem_commutant, ← comm_all_blockDiagC_iff rA sA (fun j' => bdA.hs (eA j').1) (Uᴴ * x * U)]
    constructor
    ·
     intro hx N
     have hy : U * bDC rA sA N * Uᴴ ∈ Cimg := (hCimg_iff _).mpr ⟨N, by
      calc
       Uᴴ * (U * bDC rA sA N * Uᴴ) * U
        = (Uᴴ * U) * bDC rA sA N * (Uᴴ * U) := by simp only [mma]
       _ = bDC rA sA N := by rw [hU_star_mul, m1m, mm1]⟩
     have hc := hx _ hy
     calc
      Uᴴ * x * U * bDC rA sA N
       = Uᴴ * (x * (U * bDC rA sA N * Uᴴ)) * U := by
         simp only [mma, hU_star_mul, mm1]
      _ = Uᴴ * ((U * bDC rA sA N * Uᴴ) * x) * U := by rw [hc]
      _ = bDC rA sA N * (Uᴴ * x * U) := by
         calc
          Uᴴ * ((U * bDC rA sA N * Uᴴ) * x) * U
           = (Uᴴ * U) * bDC rA sA N * (Uᴴ * x * U) := by simp only [mma]
          _ = bDC rA sA N * (Uᴴ * x * U) := by rw [hU_star_mul, m1m]
    ·
     intro hcomm y hy
     obtain ⟨N, hN⟩ := (hCimg_iff y).mp hy
     have h1 := hcomm N
     rw [← hN] at h1
     calc
      x * y = U * (Uᴴ * x * U * (Uᴴ * y * U)) * Uᴴ := by
         calc
          x * y = (U * Uᴴ) * x * (U * Uᴴ) * y * (U * Uᴴ) := by
             rw [hU_mul_star, m1m, mm1, mm1]
          _ = U * (Uᴴ * x * U * (Uᴴ * y * U)) * Uᴴ := by simp only [mma]
      _ = U * (Uᴴ * y * U * (Uᴴ * x * U)) * Uᴴ := by rw [h1]
      _ = y * x := by
         calc
          U * (Uᴴ * y * U * (Uᴴ * x * U)) * Uᴴ
           = (U * Uᴴ) * y * (U * Uᴴ) * x * (U * Uᴴ) := by simp only [mma]
          _ = y * x := by rw [hU_mul_star, m1m, mm1, mm1] }
 refine ⟨Ahat, r', bdAhat, eA, ?_, fun _ => rfl, fun _ => rfl, ?_, htr_z, hzero_z⟩
 ·
  intro x
  simp only [Ahat, mem_commutant]
  constructor
  · intro hx c hc; exact hx _ ⟨c, hc, rfl⟩
  · rintro hx _ ⟨c, hc, rfl⟩; exact hx c hc
 ·
  intro j'
  have hz_conj : bdA.Uᴴ * cPr bdA (eA j').1 * bdA.U =
    bDC bdA.r bdA.s (fun k => if k = (eA j').1 then 1 else 0) := by
   rw [centralProj_eq_blockDiagC]
   calc
    bdA.Uᴴ * (bdA.U * bDC bdA.r bdA.s (fun k => if k = (eA j').1 then 1 else 0) * bdA.Uᴴ) * bdA.U
     = (bdA.Uᴴ * bdA.U) * bDC bdA.r bdA.s (fun k => if k = (eA j').1 then 1 else 0) * (bdA.Uᴴ * bdA.U) := by
       simp only [mma]
    _ = bDC bdA.r bdA.s (fun k => if k = (eA j').1 then 1 else 0) := by
       rw [bdA.U_star_mul, m1m, mm1]
  have hdiag := hπA'_diag (fun k => if k = (eA j').1 then 1 else 0) hz_conj
  have hfn : (fun k' : Fin t' => if (eA k').1 = (eA j').1 then
    (1 : Matrix (Fin (sA k')) (Fin (sA k')) ℂ) else 0) =
    fun k' => if k' = j' then 1 else 0 := by
   funext k'
   by_cases h : k' = j'
   · subst h; simp
   ·
    have hne : (eA k').1 ≠ (eA j').1 := fun heq => h (eA.injective (Subtype.ext heq))
    simp [h, hne]
  rw [hfn] at hdiag
  rw [centralProj_eq_blockDiagC]
  change U * bDC rA sA (fun k' => if k' = j' then 1 else 0) * Uᴴ = πA' (cPr bdA (eA j').1)
  rw [← hdiag]
  calc
   U * (Uᴴ * πA' (cPr bdA (eA j').1) * U) * Uᴴ
    = (U * Uᴴ) * πA' (cPr bdA (eA j').1) * (U * Uᴴ) := by simp only [mma]
   _ = πA' (cPr bdA (eA j').1) := by rw [hU_mul_star, m1m, mm1]
end BlockMatrixUnits
/- ### 7. Reverse scale estimate (Lemma 4.1 of Thom) -/
section ReverseScaleEstimate
variable {d : ℕ}
lemma cell_scale_ge_one
  {B C : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} (hBC : B ≤ C)
  (bdB : BDec B) (bdC : BDec C)
  (i : Fin bdB.t) (j : Fin bdC.t)
  (hne : cPr bdC j * cPr bdB i ≠ 0) :
  bdB.r i * bdC.s j ≤ bdB.s i * bdC.r j := by
 let w := cPr bdB i
 let z := cPr bdC j
 let P := z * w
 have hzC' : z ∈ comm C := cPr_comm bdC j
 have hcomm_BC : ∀ b ∈ B, ∀ c ∈ comm C, c * b = b * c := fun b hb c hc => hc b (hBC hb)
 let Pab (a : Fin (bdB.r i)) (b : Fin (bdC.s j)) : Matrix (Fin d) (Fin d) ℂ :=
  mUC bdC j b b * mUA bdB i a a
 have hPab_herm : ∀ a b, (Pab a b).IsHermitian := by
  intro a b
  dsimp only [Pab, IsHermitian]
  rw [ctM, matUnitA_conjTranspose, matUnitC_conjTranspose,
   hcomm_BC _ (mUA_mem bdB i a a) _ (matUnitC_mem bdC j b b)]
 have hPab_idem : ∀ a b, Pab a b * Pab a b = Pab a b := by
  intro a b
  dsimp only [Pab]
  calc
   (mUC bdC j b b * mUA bdB i a a) * (mUC bdC j b b * mUA bdB i a a)
    = (mUC bdC j b b * mUC bdC j b b) * (mUA bdB i a a * mUA bdB i a a) := by
      rw [mma, ← mma (mUA bdB i a a),
       ← hcomm_BC _ (mUA_mem bdB i a a) _ (matUnitC_mem bdC j b b)]
      simp only [mma]
   _ = mUC bdC j b b * mUA bdB i a a := by
      rw [matUnitC_mul_same, mUA_mul]; simp
 let a0 : Fin (bdB.r i) := ⟨0, bdB.hr i⟩
 let b0 : Fin (bdC.s j) := ⟨0, bdC.hs j⟩
 let k : ℕ := Module.finrank ℂ (LinearMap.range (CLM (Pab a0 b0)).toLinearMap)
 have htr_Pab : ∀ a b, (Pab a b).trace = (k : ℂ) := by
  intro a b
  have htr0 : (Pab a0 b0).trace = (k : ℂ) :=
   proj_trace_eq_finrank_range (hPab_herm a0 b0) (hPab_idem a0 b0)
  let Uab := mUC bdC j b b0 * mUA bdB i a a0
  let Vab := mUC bdC j b0 b * mUA bdB i a0 a
  have hUV : Uab * Vab = Pab a b := by
   dsimp only [Uab, Vab, Pab]
   calc
    (mUC bdC j b b0 * mUA bdB i a a0) * (mUC bdC j b0 b * mUA bdB i a0 a)
     = (mUC bdC j b b0 * mUC bdC j b0 b) * (mUA bdB i a a0 * mUA bdB i a0 a) := by
       rw [mma, ← mma (mUA bdB i a a0),
        ← hcomm_BC _ (mUA_mem bdB i a a0) _ (matUnitC_mem bdC j b0 b)]
       simp only [mma]
    _ = mUC bdC j b b * mUA bdB i a a := by
       rw [matUnitC_mul_same, mUA_mul]; simp
  have hVU : Vab * Uab = Pab a0 b0 := by
   dsimp only [Uab, Vab, Pab]
   calc
    (mUC bdC j b0 b * mUA bdB i a0 a) * (mUC bdC j b b0 * mUA bdB i a a0)
     = (mUC bdC j b0 b * mUC bdC j b b0) * (mUA bdB i a0 a * mUA bdB i a a0) := by
       rw [mma, ← mma (mUA bdB i a0 a),
        ← hcomm_BC _ (mUA_mem bdB i a0 a) _ (matUnitC_mem bdC j b b0)]
       simp only [mma]
    _ = mUC bdC j b0 b0 * mUA bdB i a0 a0 := by
       rw [matUnitC_mul_same, mUA_mul]; simp
  rw [← hUV, trace_mul_comm, hVU, htr0]
 have hP_sum : P = ∑ a : Fin (bdB.r i), ∑ b : Fin (bdC.s j), Pab a b := by
  dsimp only [P, z, w, Pab]
  rw [← sum_matUnitC_diag bdC j, ← sum_matUnitA_diag bdB i, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  exact sum_comm
 have htr_P : P.trace = ((bdB.r i * bdC.s j * k : ℕ) : ℂ) := by
  rw [hP_sum, trace_sum]
  simp_rw [trace_sum, htr_Pab]
  simp [sum_const, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
 have hw2 : w * w = w := by dsimp only [w]; rw [cPr_mul]; simp
 have hz2 : z * z = z := by dsimp only [z]; rw [cPr_mul]; simp
 have hzw_comm : z * w = w * z := hcomm_BC w (cPr_mem bdB i) z hzC'
 have hPh : P.IsHermitian := by
  dsimp only [P, IsHermitian]
  rw [ctM, cPr_herm, cPr_herm, hzw_comm]
 have hPp : P * P = P := by
  dsimp only [P]
  calc
   (z * w) * (z * w) = (z * z) * (w * w) := by
      rw [mma, ← mma w, ← hzw_comm]
      simp only [mma]
   _ = z * w := by rw [hz2, hw2]
 have hk_pos : 1 ≤ k := by
  by_contra hk0
  have hk_eq : k = 0 := by omega
  apply hne
  apply proj_eq_zero_of_trace_re_zero hPh hPp
  rw [htr_P, hk_eq]; simp
 have hle_w : bdB.r i * bdC.s j * k ≤ bdB.r i * bdB.s i := by
  have hQh : (w - P).IsHermitian := by
   dsimp only [IsHermitian]
   rw [ctS, cPr_herm, hPh.eq]
  have hQp : (w - P) * (w - P) = w - P := by
   have hwP : w * P = P := by
    dsimp only [P]
    rw [← mma, ← hzw_comm, mma, hw2]
   have hPw : P * w = P := by
    dsimp only [P]; rw [mma, hw2]
   rw [msm, mms, mms, hw2, hwP, hPw, hPp]
   simp
  have htr_nn : 0 ≤ ((w - P).trace).re := by
   rw [proj_trace_eq_finrank_range hQh hQp]; simp
  rw [trace_sub, sub_re, trace_centralProj, htr_P] at htr_nn
  simp only [Complex.natCast_re, sub_nonneg] at htr_nn
  exact_mod_cast htr_nn
 have hle_z : bdB.r i * bdC.s j * k ≤ bdC.r j * bdC.s j := by
  have hQh : (z - P).IsHermitian := by
   dsimp only [IsHermitian]
   rw [ctS, cPr_herm, hPh.eq]
  have hQp : (z - P) * (z - P) = z - P := by
   have hzP : z * P = P := by
    dsimp only [P]; rw [← mma, hz2]
   have hPz : P * z = P := by
    dsimp only [P]
    rw [mma, ← hzw_comm, ← mma, hz2]
   rw [msm, mms, mms, hz2, hzP, hPz, hPp]
   simp
  have htr_nn : 0 ≤ ((z - P).trace).re := by
   rw [proj_trace_eq_finrank_range hQh hQp]; simp
  rw [trace_sub, sub_re, trace_centralProj, htr_P] at htr_nn
  simp only [Complex.natCast_re, sub_nonneg] at htr_nn
  exact_mod_cast htr_nn
 have h1 : bdC.s j * k ≤ bdB.s i := by
  have hpos := bdB.hr i
  have : bdB.r i * (bdC.s j * k) ≤ bdB.r i * bdB.s i := by linarith
  exact Nat.le_of_mul_le_mul_left this hpos
 have h2 : bdB.r i * k ≤ bdC.r j := by
  have hpos := bdC.hs j
  have : bdC.s j * (bdB.r i * k) ≤ bdC.s j * bdC.r j := by linarith
  exact Nat.le_of_mul_le_mul_left this hpos
 have hk2 : 1 ≤ k * k := by nlinarith
 calc
  bdB.r i * bdC.s j = bdB.r i * bdC.s j * 1 := (mul_one _).symm
  _ ≤ bdB.r i * bdC.s j * (k * k) := Nat.mul_le_mul_left _ hk2
  _ = (bdB.r i * k) * (bdC.s j * k) := by ring
  _ ≤ bdC.r j * bdB.s i := Nat.mul_le_mul h2 h1
  _ = bdB.s i * bdC.r j := mul_comm _ _
lemma hsSq_condExp_eq_sum_matUnitA {B : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdB : BDec B) (X : Matrix (Fin d) (Fin d) ℂ) :
  hsSq (cExp B X) =
   ∑ i : Fin bdB.t, ((bdB.s i : ℝ)⁻¹) *
    ∑ a : Fin (bdB.r i), ∑ c : Fin (bdB.r i), ‖((mUA bdB i a c)ᴴ * X).trace‖ ^ 2 := by
 rw [condExp_eq_blockDiagA bdB X]
 have hhs : hsSq (bdB.U * bDA bdB.r bdB.s (bCEM bdB X) * bdB.Uᴴ) =
   ∑ i : Fin bdB.t, (bdB.s i : ℝ) * hsSq (bCEM bdB X i) := by
  rw [hsSq_coisoR bdB.Uᴴ (by simpa using bdB.U_star_mul),
   hsSq_isoL bdB.U bdB.U_star_mul]
  unfold hsSq bDA
  rw [Fintype.sum_sigma]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_prod_type]
  have hinner : ∀ (a : Fin (bdB.r i)) (b : Fin (bdB.s i)),
    (∑ p : (Σ j : Fin bdB.t, Fin (bdB.r j) × Fin (bdB.s j)),
     ‖if h : i = p.1 then if b = h ▸ p.2.2 then bCEM bdB X i a (h ▸ p.2.1) else 0 else 0‖ ^ 2) =
    ∑ c : Fin (bdB.r i), ‖bCEM bdB X i a c‖ ^ 2 := by
   intro a b
   rw [Fintype.sum_sigma, sum_eq_single i]
   ·
    simp only [↓reduceDIte, sum_prod_type]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_eq_single b]
    · simp
    · intro d' _ hdb; simp [hdb.symm]
    · intro h; exact absurd (mem_univ b) h
   · intro j _ hji; exact sum_eq_zero fun p _ => by simp [Ne.symm hji]
   · intro h; exact absurd (mem_univ i) h
  simp_rw [hinner]
  simp [sum_const, nsmul_eq_mul, Finset.mul_sum, mul_comm]
 rw [hhs]
 refine sum_congr rfl fun i _ => ?_
 unfold hsSq
 rw [Finset.mul_sum, Finset.mul_sum]
 refine sum_congr rfl fun a _ => ?_
 rw [Finset.mul_sum, Finset.mul_sum]
 refine sum_congr rfl fun c _ => ?_
 have htr : ((mUA bdB i a c)ᴴ * X).trace =
   ∑ k : Fin (bdB.s i), (bdB.Uᴴ * X * bdB.U) ⟨i, a, k⟩ ⟨i, c, k⟩ := by
  rw [matUnitA_conjTranspose]
  have h1 : ((mUA bdB i c a) * X).trace =
    ((bdB.Uᴴ * mUA bdB i c a * bdB.U) * (bdB.Uᴴ * X * bdB.U)).trace := by
   calc
    (mUA bdB i c a * X).trace
     = ((mUA bdB i c a * (bdB.U * bdB.Uᴴ) * X * bdB.U) * bdB.Uᴴ).trace := by
       simp only [mma, bdB.U_mul_star, mm1]
    _ = (bdB.Uᴴ * (mUA bdB i c a * (bdB.U * bdB.Uᴴ) * X * bdB.U)).trace :=
       trace_mul_comm _ _
    _ = (bdB.Uᴴ * mUA bdB i c a * bdB.U * (bdB.Uᴴ * X * bdB.U)).trace := by
       simp only [mma]
  rw [h1, matUnitA_conj, Matrix.trace, Fintype.sum_sigma, sum_eq_single i]
  ·
   simp only [Matrix.diag_apply, mul_apply, sum_prod_type]
   rw [sum_eq_single c]
   ·
    refine sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_sigma, sum_eq_single i]
    ·
     simp only [bDA, ↓reduceDIte, sum_prod_type]
     rw [sum_eq_single a]
     ·
      rw [sum_eq_single k]
      · simp
      · intro l _ hlk; simp [hlk.symm]
      · intro h; exact absurd (mem_univ k) h
     · intro x _ hxa; exact sum_eq_zero fun l _ => by simp [hxa.symm]
     · intro h; exact absurd (mem_univ a) h
    · intro j _ hji; exact sum_eq_zero fun p _ => by simp [bDA, Ne.symm hji]
    · intro h; exact absurd (mem_univ i) h
   ·
    intro x _ hxc
    refine sum_eq_zero fun k _ => ?_
    rw [Fintype.sum_sigma]
    refine sum_eq_zero fun j _ => sum_eq_zero fun p _ => ?_
    by_cases hji : i = j
    · subst hji; simp [bDA, hxc.symm]
    · simp [bDA, hji]
   · intro h; exact absurd (mem_univ c) h
  ·
   intro j _ hji
   refine sum_eq_zero fun p _ => ?_
   rw [Matrix.diag_apply, mul_apply]
   refine sum_eq_zero fun q _ => ?_
   by_cases hqj : j = q.1
   · subst hqj; simp [bDA, hji]
   · simp [bDA, hqj]
  · intro h; exact absurd (mem_univ i) h
 rw [htr]
 dsimp only [bCEM]
 rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow, inv_pow]
 have hsi0 : (bdB.s i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (bdB.hs i))
 field_simp [hsi0]
lemma avg_norm_trace_hw {C : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdC : BDec C) {E : Matrix (Fin d) (Fin d) ℂ} (hE : E ∈ C) :
  ((Fintype.card (BHW bdC) : ℝ)⁻¹) *
    ∑ g : BHW bdC, ‖(Eᴴ * bHW bdC g).trace‖ ^ 2 =
   ∑ j : Fin bdC.t, ((bdC.s j : ℝ) / (bdC.r j : ℝ)) * hsSq (cPr bdC j * E) := by
 obtain ⟨M, hM⟩ := (bdC.mem_iff E).mp hE
 have hN0 : (Fintype.card (BHW bdC) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (ne_of_gt (blockHW_card_pos bdC))
 have hcard : ∀ j : Fin bdC.t, Fintype.card (HWI (bdC.r j)) = 2 * bdC.r j * bdC.r j * bdC.r j := by
  intro j; simp only [Fintype.card_prod, card_fin]; ring
 have htr_g : ∀ g : BHW bdC,
   (Eᴴ * bHW bdC g).trace =
    ∑ j : Fin bdC.t, (bdC.s j : ℂ) * ((M j)ᴴ * hwM (bdC.r j) (g j)).trace := by
  intro g
  have hE' : (bdC.Uᴴ * E * bdC.U)ᴴ = bDA bdC.r bdC.s (fun j => (M j)ᴴ) := by
   rw [hM, blockDiagA_conjTranspose]
  have h1 : (Eᴴ * bHW bdC g).trace =
    ((bdC.Uᴴ * E * bdC.U)ᴴ * bDA bdC.r bdC.s (fun j => hwM (bdC.r j) (g j))).trace := by
   simp only [bHW]
   let H := bDA bdC.r bdC.s (fun j => hwM (bdC.r j) (g j))
   change (Eᴴ * (bdC.U * H * bdC.Uᴴ)).trace = ((bdC.Uᴴ * E * bdC.U)ᴴ * H).trace
   calc
    (Eᴴ * (bdC.U * H * bdC.Uᴴ)).trace
     = ((Eᴴ * bdC.U * H) * bdC.Uᴴ).trace := by simp only [mma]
    _ = (bdC.Uᴴ * (Eᴴ * bdC.U * H)).trace := trace_mul_comm _ _
    _ = ((bdC.Uᴴ * E * bdC.U)ᴴ * H).trace := by
       simp only [ctM, ctct, mma]
  rw [h1, hE', blockDiagA_mul, Matrix.trace, Fintype.sum_sigma]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_prod_type]
  simp only [Matrix.diag_apply, bDA, ↓reduceDIte, ↓reduceIte, sum_const,
   card_univ, card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  rfl
 have hC : ((((Fintype.card (BHW bdC) : ℝ)⁻¹) *
    ∑ g : BHW bdC, ‖(Eᴴ * bHW bdC g).trace‖ ^ 2 : ℝ) : ℂ) =
   ((∑ j : Fin bdC.t, ((bdC.s j : ℝ) / (bdC.r j : ℝ)) * hsSq (cPr bdC j * E) : ℝ) : ℂ) := by
  push_cast
  have hnormSq : ∀ z : ℂ, ((‖z‖ : ℝ) : ℂ) ^ 2 = z * star z := fun z => by
   rw [star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simp_rw [hnormSq, htr_g, star_sum]
  have hexp : ∀ g : BHW bdC,
    (∑ j : Fin bdC.t, (bdC.s j : ℂ) * ((M j)ᴴ * hwM (bdC.r j) (g j)).trace) *
     (∑ j : Fin bdC.t, star ((bdC.s j : ℂ) * ((M j)ᴴ * hwM (bdC.r j) (g j)).trace)) =
    ∑ j₁ : Fin bdC.t, ∑ j₂ : Fin bdC.t,
     (bdC.s j₁ : ℂ) * ((M j₁)ᴴ * hwM (bdC.r j₁) (g j₁)).trace *
      star ((bdC.s j₂ : ℂ) * ((M j₂)ᴴ * hwM (bdC.r j₂) (g j₂)).trace) := by
   intro g
   rw [Finset.sum_mul]
   refine sum_congr rfl fun j₁ _ => Finset.mul_sum _ _ _
  simp_rw [hexp]
  rw [sum_comm]
  simp_rw [sum_comm (s := univ (α := BHW bdC))]
  rw [Finset.mul_sum]
  refine sum_congr rfl fun j₁ _ => ?_
  rw [Finset.mul_sum, sum_eq_single j₁]
  ·
   -- j₁ = j₂
   let ePi : BHW bdC ≃ HWI (bdC.r j₁) ×
     ((k : {k : Fin bdC.t // k ≠ j₁}) → HWI (bdC.r k.1)) :=
    {
     toFun := fun g => (g j₁, fun k => g k.1)
     invFun := fun p k => if h : k = j₁ then h ▸ p.1 else p.2 ⟨k, h⟩
     left_inv := fun g => by funext k; by_cases h : k = j₁ <;> simp [h]; subst h; rfl
     right_inv := fun p => Prod.ext (by simp) (funext fun k => by simp [k.2]) }
   have hsplit : ∑ g : BHW bdC,
     (bdC.s j₁ : ℂ) * ((M j₁)ᴴ * hwM (bdC.r j₁) (g j₁)).trace *
      star ((bdC.s j₁ : ℂ) * ((M j₁)ᴴ * hwM (bdC.r j₁) (g j₁)).trace) =
     ((Fintype.card (BHW bdC) / Fintype.card (HWI (bdC.r j₁)) : ℕ) : ℂ) *
      ∑ u : HWI (bdC.r j₁),
       (bdC.s j₁ : ℂ) * ((M j₁)ᴴ * hwM (bdC.r j₁) u).trace *
        star ((bdC.s j₁ : ℂ) * ((M j₁)ᴴ * hwM (bdC.r j₁) u).trace) := by
    rw [← Equiv.sum_comp ePi.symm, sum_prod_type]
    have hs' : ∀ u rest, ePi.symm (u, rest) j₁ = u := fun u rest => by simp [ePi]
    simp_rw [hs', sum_const, card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    congr 1
    have hdiv : Fintype.card (BHW bdC) =
      Fintype.card ((k : {k : Fin bdC.t // k ≠ j₁}) → HWI (bdC.r k.1)) *
       Fintype.card (HWI (bdC.r j₁)) := by
     rw [Fintype.card_congr ePi, Fintype.card_prod, mul_comm]
    have hpos : 0 < Fintype.card (HWI (bdC.r j₁)) := by
     rw [hcard j₁]; have := bdC.hr j₁; positivity
    rw [hdiv, Nat.mul_div_cancel _ hpos]
   rw [hsplit]
   have h2mom : ∑ u : HWI (bdC.r j₁),
     ((M j₁)ᴴ * hwM (bdC.r j₁) u).trace * star (((M j₁)ᴴ * hwM (bdC.r j₁) u).trace) =
     ((2 * bdC.r j₁ * bdC.r j₁ : ℕ) : ℂ) * ((hsSq (M j₁) : ℝ) : ℂ) := by
    have hexp_u : ∀ u : HWI (bdC.r j₁),
      ((M j₁)ᴴ * hwM (bdC.r j₁) u).trace * star (((M j₁)ᴴ * hwM (bdC.r j₁) u).trace) =
      ∑ x : Fin (bdC.r j₁), ∑ y : Fin (bdC.r j₁), ∑ z : Fin (bdC.r j₁), ∑ w : Fin (bdC.r j₁),
       (star (M j₁ y x) * M j₁ w z) *
        (hwM (bdC.r j₁) u y x * star (hwM (bdC.r j₁) u w z)) := by
     intro u
     simp only [Matrix.trace, Matrix.diag_apply, mul_apply, ctA,
      star_sum, star_mul', star_star]
     rw [Finset.sum_mul]
     refine sum_congr rfl fun x _ => ?_
     rw [Finset.sum_mul]
     refine sum_congr rfl fun y _ => ?_
     rw [Finset.mul_sum]
     refine sum_congr rfl fun z _ => ?_
     rw [Finset.mul_sum]
     refine sum_congr rfl fun w _ => by ring
    simp_rw [hexp_u]
    rw [sum_comm]
    have hstep : ∀ x : Fin (bdC.r j₁),
      (∑ u : HWI (bdC.r j₁), ∑ y : Fin (bdC.r j₁), ∑ z : Fin (bdC.r j₁), ∑ w : Fin (bdC.r j₁),
       (star (M j₁ y x) * M j₁ w z) *
        (hwM (bdC.r j₁) u y x * star (hwM (bdC.r j₁) u w z))) =
      ∑ y : Fin (bdC.r j₁), ((2 * bdC.r j₁ * bdC.r j₁ : ℕ) : ℂ) * ((‖M j₁ y x‖ ^ 2 : ℝ) : ℂ) := by
     intro x
     rw [sum_comm]
     refine sum_congr rfl fun y _ => ?_
     rw [sum_comm]
     have hz : ∀ z : Fin (bdC.r j₁),
       (∑ u : HWI (bdC.r j₁), ∑ w : Fin (bdC.r j₁),
        (star (M j₁ y x) * M j₁ w z) *
         (hwM (bdC.r j₁) u y x * star (hwM (bdC.r j₁) u w z))) =
       ∑ w : Fin (bdC.r j₁), (star (M j₁ y x) * M j₁ w z) *
        if y = w ∧ x = z then ((2 * bdC.r j₁ * bdC.r j₁ : ℕ) : ℂ) else 0 := by
      intro z
      rw [sum_comm]
      refine sum_congr rfl fun w _ => ?_
      rw [← Finset.mul_sum, hwMat_second_moment (bdC.hr j₁)]
     simp_rw [hz]
     rw [sum_eq_single x]
     ·
      rw [sum_eq_single y]
      ·
       simp only [and_self, ↓reduceIte]
       rw [Complex.ofReal_pow, hnormSq (M j₁ y x)]; ring
      · intro w _ hwy; simp [hwy.symm]
      · intro h; exact absurd (mem_univ y) h
     · intro z _ hzx; exact sum_eq_zero fun w _ => by simp [hzx.symm]
     · intro h; exact absurd (mem_univ x) h
    simp_rw [hstep]
    rw [sum_comm]
    simp only [hsSq, Complex.ofReal_sum, Finset.mul_sum]
   have hhs_zE : hsSq (cPr bdC j₁ * E) = (bdC.s j₁ : ℝ) * hsSq (M j₁) := by
    rw [← hsSq_isoL bdC.Uᴴ (by simpa using bdC.U_mul_star),
     ← hsSq_coisoR bdC.U bdC.U_mul_star]
    have heq : bdC.Uᴴ * (cPr bdC j₁ * E) * bdC.U =
      bDA bdC.r bdC.s (fun k => if k = j₁ then M k else 0) := by
     calc
      bdC.Uᴴ * (cPr bdC j₁ * E) * bdC.U
       = (bdC.Uᴴ * cPr bdC j₁ * bdC.U) * (bdC.Uᴴ * E * bdC.U) := by
         calc
          bdC.Uᴴ * (cPr bdC j₁ * E) * bdC.U
           = bdC.Uᴴ * cPr bdC j₁ * (bdC.U * bdC.Uᴴ) * E * bdC.U := by
             rw [bdC.U_mul_star, mm1]; simp only [mma]
          _ = _ := by simp only [mma]
      _ = bDA bdC.r bdC.s (fun k => (if k = j₁ then 1 else 0) * M k) := by
         rw [centralProj_conj, hM, blockDiagA_mul]
      _ = bDA bdC.r bdC.s (fun k => if k = j₁ then M k else 0) := by
         congr 1; funext k; by_cases h : k = j₁ <;> simp [h]
    rw [heq]
    unfold hsSq bDA
    rw [Fintype.sum_sigma, sum_eq_single j₁]
    ·
     simp only [↓reduceIte, sum_prod_type]
     have hinner : ∀ (a : Fin (bdC.r j₁)) (b : Fin (bdC.s j₁)),
       (∑ p : (Σ k : Fin bdC.t, Fin (bdC.r k) × Fin (bdC.s k)),
        ‖if h : j₁ = p.1 then if b = h ▸ p.2.2 then M j₁ a (h ▸ p.2.1) else 0 else 0‖ ^ 2) =
       ∑ c : Fin (bdC.r j₁), ‖M j₁ a c‖ ^ 2 := by
      intro a b
      rw [Fintype.sum_sigma, sum_eq_single j₁]
      ·
       simp only [↓reduceDIte, sum_prod_type]
       refine sum_congr rfl fun c _ => ?_
       rw [sum_eq_single b]
       · simp
       · intro d' _ hdb; simp [hdb.symm]
       · intro h; exact absurd (mem_univ b) h
      · intro k _ hkj; exact sum_eq_zero fun p _ => by simp [Ne.symm hkj]
      · intro h; exact absurd (mem_univ j₁) h
     simp_rw [hinner]
     simp [sum_const, nsmul_eq_mul, Finset.mul_sum, mul_comm]
    ·
     intro k _ hkj
     refine sum_eq_zero fun p _ => sum_eq_zero fun q _ => ?_
     by_cases hkq : k = q.1
     · subst hkq; simp [hkj]
     · simp [hkq]
    · intro h; exact absurd (mem_univ j₁) h
   have hdiv_cast : ((Fintype.card (BHW bdC) / Fintype.card (HWI (bdC.r j₁)) : ℕ) : ℂ) =
     (Fintype.card (BHW bdC) : ℂ) / (Fintype.card (HWI (bdC.r j₁)) : ℂ) := by
    have hdvd : Fintype.card (HWI (bdC.r j₁)) ∣ Fintype.card (BHW bdC) := by
     rw [Fintype.card_pi]; exact Finset.dvd_prod_of_mem _ (mem_univ j₁)
    rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (by rw [hcard j₁]; have := bdC.hr j₁; positivity))]
   have hpull : ∑ u : HWI (bdC.r j₁),
     (bdC.s j₁ : ℂ) * ((M j₁)ᴴ * hwM (bdC.r j₁) u).trace *
      star ((bdC.s j₁ : ℂ) * ((M j₁)ᴴ * hwM (bdC.r j₁) u).trace) =
     ((bdC.s j₁ : ℂ) * (bdC.s j₁ : ℂ)) *
      ∑ u : HWI (bdC.r j₁),
       ((M j₁)ᴴ * hwM (bdC.r j₁) u).trace * star (((M j₁)ᴴ * hwM (bdC.r j₁) u).trace) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [star_mul', star_def, map_natCast]; ring
   rw [hpull, h2mom, hdiv_cast, hcard j₁, hhs_zE]
   have hr0 : (bdC.r j₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (bdC.hr j₁))
   push_cast
   field_simp [hN0, hr0]
  ·
   intro j₂ _ hj₂
   let ePi : BHW bdC ≃ HWI (bdC.r j₁) ×
     ((k : {k : Fin bdC.t // k ≠ j₁}) → HWI (bdC.r k.1)) :=
    {
     toFun := fun g => (g j₁, fun k => g k.1)
     invFun := fun p k => if h : k = j₁ then h ▸ p.1 else p.2 ⟨k, h⟩
     left_inv := fun g => by funext k; by_cases h : k = j₁ <;> simp [h]; subst h; rfl
     right_inv := fun p => Prod.ext (by simp) (funext fun k => by simp [k.2]) }
   rw [mul_eq_zero]
   right
   rw [← Equiv.sum_comp ePi.symm, sum_prod_type]
   have hsimp : ∀ u rest,
     (bdC.s j₁ : ℂ) * ((M j₁)ᴴ * hwM (bdC.r j₁) (ePi.symm (u, rest) j₁)).trace *
      star ((bdC.s j₂ : ℂ) * ((M j₂)ᴴ * hwM (bdC.r j₂) (ePi.symm (u, rest) j₂)).trace) =
     ((bdC.s j₁ : ℂ) * star ((bdC.s j₂ : ℂ) *
       ((M j₂)ᴴ * hwM (bdC.r j₂) (rest ⟨j₂, hj₂⟩)).trace)) *
      ((M j₁)ᴴ * hwM (bdC.r j₁) u).trace := by
    intro u rest; simp only [ePi, Equiv.coe_fn_symm_mk, ↓reduceDIte, dif_neg hj₂]; ring
   simp_rw [hsimp]
   rw [sum_comm]
   refine sum_eq_zero fun rest _ => ?_
   rw [← Finset.mul_sum]
   have htr0 : ∑ u : HWI (bdC.r j₁), ((M j₁)ᴴ * hwM (bdC.r j₁) u).trace = 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, mul_apply]
    rw [sum_comm]
    refine sum_eq_zero fun x _ => ?_
    rw [sum_comm]
    refine sum_eq_zero fun y _ => ?_
    rw [← Finset.mul_sum, hwMat_first_moment (bdC.hr j₁) y x, mul_zero]
   rw [htr0, mul_zero]
  · intro h; exact absurd (mem_univ j₁) h
 exact_mod_cast hC
lemma avg_hsSq_sub_condExp_eq
  {B C : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} (hBC : B ≤ C)
  (bdB : BDec B) (bdC : BDec C) :
  ((Fintype.card (BHW bdC) : ℝ)⁻¹) *
    ∑ g : BHW bdC, hsSq (bHW bdC g - cExp B (bHW bdC g)) =
   ∑ i : Fin bdB.t, ∑ j : Fin bdC.t,
    (1 - ((bdB.r i * bdC.s j : ℝ) / (bdB.s i * bdC.r j : ℝ))) *
     ((cPr bdC j * cPr bdB i).trace).re := by
 have hNpos : (0 : ℝ) < Fintype.card (BHW bdC) := Nat.cast_pos.mpr (blockHW_card_pos bdC)
 have hN0 : (Fintype.card (BHW bdC) : ℝ) ≠ 0 := ne_of_gt hNpos
 have hpyth : ∀ g : BHW bdC,
   hsSq (bHW bdC g - cExp B (bHW bdC g)) =
    (d : ℝ) - hsSq (cExp B (bHW bdC g)) := by
  intro g
  have h1 := hsSq_eq_hsSq_condExp_add B (bHW bdC g)
  have hu : hsSq (bHW bdC g) = d := by
   have hU := bHW_u bdC g
   rw [hsSq_tr]
   have hU' : (bHW bdC g)ᴴ * bHW bdC g = 1 := star_mul_self_of_mem hU
   rw [hU', trace_one, card_fin]; simp
  linarith
 simp_rw [hpyth, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
  mul_sub, inv_mul_cancel_left₀ hN0]
 have hsum_ce : ((Fintype.card (BHW bdC) : ℝ)⁻¹) *
    ∑ g : BHW bdC, hsSq (cExp B (bHW bdC g)) =
   ∑ i : Fin bdB.t, ∑ j : Fin bdC.t,
    ((bdB.r i * bdC.s j : ℝ) / (bdB.s i * bdC.r j : ℝ)) *
     ((cPr bdC j * cPr bdB i).trace).re := by
  simp_rw [hsSq_condExp_eq_sum_matUnitA bdB]
  rw [sum_comm, Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp_rw [← Finset.mul_sum]
  rw [mul_left_comm, sum_comm]
  simp_rw [sum_comm (s := univ (α := BHW bdC))]
  have hinner : ∀ a c : Fin (bdB.r i),
    ((Fintype.card (BHW bdC) : ℝ)⁻¹) *
      ∑ g : BHW bdC, ‖((mUA bdB i a c)ᴴ * bHW bdC g).trace‖ ^ 2 =
     ∑ j : Fin bdC.t, ((bdC.s j : ℝ) / (bdC.r j : ℝ)) *
      ((cPr bdC j * mUA bdB i c c).trace).re := by
   intro a c
   rw [avg_norm_trace_hw bdC (hBC (mUA_mem bdB i a c))]
   refine sum_congr rfl fun j _ => ?_
   congr 1
   rw [hsSq_tr, ctM, cPr_herm, matUnitA_conjTranspose]
   have hcomm : cPr bdC j * mUA bdB i c a = mUA bdB i c a * cPr bdC j :=
    cPr_comm bdC j _ (hBC (mUA_mem bdB i c a))
   have heq : (mUA bdB i c a * cPr bdC j) * (cPr bdC j * mUA bdB i a c) =
     cPr bdC j * mUA bdB i c c := by
    calc
     (mUA bdB i c a * cPr bdC j) * (cPr bdC j * mUA bdB i a c)
      = mUA bdB i c a * ((cPr bdC j * cPr bdC j) * mUA bdB i a c) := by
        simp only [mma]
     _ = mUA bdB i c a * (cPr bdC j * mUA bdB i a c) := by
        rw [cPr_mul]; simp
     _ = (cPr bdC j * mUA bdB i c a) * mUA bdB i a c := by
        rw [← mma, ← hcomm]
     _ = cPr bdC j * (mUA bdB i c a * mUA bdB i a c) := by
        simp only [mma]
     _ = cPr bdC j * mUA bdB i c c := by rw [mUA_mul]; simp
   rw [heq]
  have hpull : ((Fintype.card (BHW bdC) : ℝ)⁻¹) *
    ∑ a : Fin (bdB.r i), ∑ c : Fin (bdB.r i),
     ∑ g : BHW bdC, ‖((mUA bdB i a c)ᴴ * bHW bdC g).trace‖ ^ 2 =
    ∑ a : Fin (bdB.r i), ∑ c : Fin (bdB.r i),
     ∑ j : Fin bdC.t, ((bdC.s j : ℝ) / (bdC.r j : ℝ)) *
      ((cPr bdC j * mUA bdB i c c).trace).re := by
   rw [Finset.mul_sum]
   refine sum_congr rfl fun a _ => ?_
   rw [Finset.mul_sum]
   refine sum_congr rfl fun c _ => hinner a c
  rw [hpull]
  rw [sum_const, card_univ, card_fin, nsmul_eq_mul, sum_comm]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, ← re_sum, ← trace_sum, ← Matrix.mul_sum, sum_matUnitA_diag]
  ring
 have hd_eq : (d : ℝ) = ∑ i : Fin bdB.t, ∑ j : Fin bdC.t,
   ((cPr bdC j * cPr bdB i).trace).re := by
  simp_rw [← re_sum, ← trace_sum, ← Matrix.sum_mul, sum_cPr, m1m]
  rw [sum_cPr, trace_one, card_fin]; simp
 rw [hsum_ce, hd_eq, ← sum_sub_distrib]
 refine sum_congr rfl fun i _ => ?_
 rw [← sum_sub_distrib]
 refine sum_congr rfl fun j _ => by ring
lemma unitary_commutator_avg_eq {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bd : BDec A) {v : Matrix (Fin d) (Fin d) ℂ}
  (hv : v ∈ unitaryGroup (Fin d) ℂ) :
  hsSq (v - cExp (comm A) v) =
   (2 * (Fintype.card (BHW bd) : ℝ))⁻¹ *
    ∑ g : BHW bd, hsSq (v * bHW bd g - bHW bd g * v) := by
 have hNpos : (0 : ℝ) < Fintype.card (BHW bd) := Nat.cast_pos.mpr (blockHW_card_pos bd)
 have hN0 : (Fintype.card (BHW bd) : ℝ) ≠ 0 := ne_of_gt hNpos
 have hv_star : vᴴ * v = 1 := star_mul_self_of_mem hv
 have hv_mul : v * vᴴ = 1 := mul_star_self_of_mem hv
 have hL : hsSq (v - cExp (comm A) v) =
   (d : ℝ) - ((vᴴ * cExp (comm A) v).trace).re := by
  have h1 := hsSq_eq_hsSq_condExp_add (comm A) v
  have hv_sq : hsSq v = d := by rw [hsSq_tr, hv_star, trace_one, card_fin]; simp
  have hce_sq : hsSq (cExp (comm A) v) = ((vᴴ * cExp (comm A) v).trace).re := by
   rw [hsSq_tr, condExp_inner_eq (comm A) v (condExp_mem _ v)]
  linarith
 have hcomm_sq : ∀ g : BHW bd,
   hsSq (v * bHW bd g - bHW bd g * v) =
    2 * (d : ℝ) - 2 * ((vᴴ * (bHW bd g * v * (bHW bd g)ᴴ)).trace).re := by
  intro g
  have hU := bHW_u bd g
  have hUs : (bHW bd g)ᴴ * bHW bd g = 1 := star_mul_self_of_mem hU
  have hUm : bHW bd g * (bHW bd g)ᴴ = 1 := mul_star_self_of_mem hU
  rw [hsSq_tr, ctS, msm, mms, mms,
   trace_sub, trace_sub, trace_sub, sub_re, sub_re, sub_re]
  have ht1 : ((v * bHW bd g)ᴴ * (v * bHW bd g)).trace = d := by
   rw [ctM, mma, ← mma vᴴ, hv_star,
    m1m, hUs, trace_one, card_fin]
  have ht2 : ((bHW bd g * v)ᴴ * (bHW bd g * v)).trace = d := by
   rw [ctM, mma, ← mma (bHW bd g)ᴴ, hUs,
    m1m, hv_star, trace_one, card_fin]
  have ht3 : ((v * bHW bd g)ᴴ * (bHW bd g * v)).trace =
    (vᴴ * (bHW bd g * v * (bHW bd g)ᴴ)).trace := by
   rw [ctM]
   calc
    ((bHW bd g)ᴴ * vᴴ * (bHW bd g * v)).trace
     = ((bHW bd g)ᴴ * (vᴴ * (bHW bd g * v))).trace := by simp only [mma]
    _ = ((vᴴ * (bHW bd g * v)) * (bHW bd g)ᴴ).trace := trace_mul_comm _ _
    _ = (vᴴ * (bHW bd g * v * (bHW bd g)ᴴ)).trace := by simp only [mma]
  have ht4 : ((bHW bd g * v)ᴴ * (v * bHW bd g)).trace =
    star ((vᴴ * (bHW bd g * v * (bHW bd g)ᴴ)).trace) := by
   rw [← ht3, ← trace_conjTranspose]
   congr 1
   simp only [ctM, ctct, mma]
  rw [ht1, ht2, ht3, ht4, star_def, Complex.conj_re]
  simp only [Complex.natCast_re]
  ring
 rw [hL, condExp_commutant_eq_avg bd v]
 simp_rw [hcomm_sq, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
  ← Finset.mul_sum]
 rw [Matrix.mul_smul, Matrix.mul_sum, trace_smul, trace_sum, smul_eq_mul]
 have hre : ((((Fintype.card (BHW bd) : ℂ)⁻¹) *
   ∑ g : BHW bd, (vᴴ * (bHW bd g * v * (bHW bd g)ᴴ)).trace)).re =
   ((Fintype.card (BHW bd) : ℝ)⁻¹) *
    ∑ g : BHW bd, ((vᴴ * (bHW bd g * v * (bHW bd g)ᴴ)).trace).re := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
   Complex.ofReal_im, zero_mul, sub_zero, re_sum]
 rw [hre]
 field_simp [hN0]
lemma reverse_scale_estimate
  {B C : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} (hBC : B ≤ C)
  (bdB : BDec B) (bdC : BDec C)
  {a : Matrix (Fin d) (Fin d) ℂ} (ha : a ∈ C) (ha_norm : ‖CLM a‖ ≤ 1) :
  hsSq (a - cExp B a) ≤
   8 * ∑ i : Fin bdB.t, ∑ j : Fin bdC.t,
    (1 - ((bdB.r i * bdC.s j : ℝ) / (bdB.s i * bdC.r j : ℝ))) *
     ((cPr bdC j * cPr bdB i).trace).re := by
 let δ : ℝ := ∑ i : Fin bdB.t, ∑ j : Fin bdC.t,
  (1 - ((bdB.r i * bdC.s j : ℝ) / (bdB.s i * bdC.r j : ℝ))) *
   ((cPr bdC j * cPr bdB i).trace).re
 obtain ⟨bdB'⟩ := exists_blockDecomp (comm B)
 have hB'_pos : (0 : ℝ) < Fintype.card (BHW bdB') := Nat.cast_pos.mpr (blockHW_card_pos bdB')
 have hC_pos : (0 : ℝ) < Fintype.card (BHW bdC) := Nat.cast_pos.mpr (blockHW_card_pos bdC)
 have hfubini : ((Fintype.card (BHW bdB') : ℝ)⁻¹) *
   ∑ h : BHW bdB', hsSq (bHW bdB' h - cExp (comm C) (bHW bdB' h)) = δ := by
  have h1 : ∀ h : BHW bdB',
    hsSq (bHW bdB' h - cExp (comm C) (bHW bdB' h)) =
     (2 * (Fintype.card (BHW bdC) : ℝ))⁻¹ *
      ∑ g : BHW bdC, hsSq (bHW bdB' h * bHW bdC g - bHW bdC g * bHW bdB' h) :=
   fun h => unitary_commutator_avg_eq bdC (bHW_u bdB' h)
  have h2 : ∀ g : BHW bdC,
    hsSq (bHW bdC g - cExp B (bHW bdC g)) =
     (2 * (Fintype.card (BHW bdB') : ℝ))⁻¹ *
      ∑ h : BHW bdB', hsSq (bHW bdC g * bHW bdB' h - bHW bdB' h * bHW bdC g) := by
   intro g
   have := unitary_commutator_avg_eq bdB' (bHW_u bdC g)
   rwa [bicommutant_eq B] at this
  simp_rw [h1]
  rw [← Finset.mul_sum, sum_comm, ← mul_assoc]
  have hsymm : ∀ g h, hsSq (bHW bdB' h * bHW bdC g - bHW bdC g * bHW bdB' h) =
    hsSq (bHW bdC g * bHW bdB' h - bHW bdB' h * bHW bdC g) := by
   intro g h
   rw [← hsSq_neg, neg_sub]
  simp_rw [hsymm]
  have hrearr : ((Fintype.card (BHW bdB') : ℝ)⁻¹) * (2 * (Fintype.card (BHW bdC) : ℝ))⁻¹ *
    ∑ g : BHW bdC, ∑ h : BHW bdB',
     hsSq (bHW bdC g * bHW bdB' h - bHW bdB' h * bHW bdC g) =
    ((Fintype.card (BHW bdC) : ℝ)⁻¹) *
     ∑ g : BHW bdC, (2 * (Fintype.card (BHW bdB') : ℝ))⁻¹ *
      ∑ h : BHW bdB',
       hsSq (bHW bdC g * bHW bdB' h - bHW bdB' h * bHW bdC g) := by
   rw [← Finset.mul_sum, ← mul_assoc]
   congr 1; ring
  rw [hrearr]
  simp_rw [← h2]
  exact avg_hsSq_sub_condExp_eq hBC bdB bdC
 have hunitary : ∀ v ∈ C, v ∈ unitaryGroup (Fin d) ℂ →
   hsSq (v - cExp B v) ≤ 2 * δ := by
  intro v hvC hvU
  have havg := unitary_commutator_avg_eq bdB' hvU
  rw [bicommutant_eq B] at havg
  rw [havg]
  have hterm : ∀ h : BHW bdB',
    hsSq (v * bHW bdB' h - bHW bdB' h * v) ≤
     4 * hsSq (bHW bdB' h - cExp (comm C) (bHW bdB' h)) := by
   intro h
   let c := cExp (comm C) (bHW bdB' h)
   have hc : c * v = v * c := (condExp_mem (comm C) _) v hvC
   have hsplit : v * bHW bdB' h - bHW bdB' h * v =
     v * (bHW bdB' h - c) - (bHW bdB' h - c) * v := by
    rw [mms, msm, hc]; abel
   rw [hsplit]
   calc
    hsSq (v * (bHW bdB' h - c) - (bHW bdB' h - c) * v)
     ≤ 2 * hsSq (v * (bHW bdB' h - c)) + 2 * hsSq ((bHW bdB' h - c) * v) :=
       hsSq_sub_le _ _
    _ = 4 * hsSq (bHW bdB' h - c) := by
       rw [hsSq_isoL v (star_mul_self_of_mem hvU),
        hsSq_coisoR v (mul_star_self_of_mem hvU)]
       ring
  calc
   (2 * (Fintype.card (BHW bdB') : ℝ))⁻¹ *
     ∑ h : BHW bdB', hsSq (v * bHW bdB' h - bHW bdB' h * v)
    ≤ (2 * (Fintype.card (BHW bdB') : ℝ))⁻¹ *
     ∑ h : BHW bdB', 4 * hsSq (bHW bdB' h - cExp (comm C) (bHW bdB' h)) := by
      gcongr with h _; exact hterm h
   _ = 2 * (((Fintype.card (BHW bdB') : ℝ)⁻¹) *
      ∑ h : BHW bdB', hsSq (bHW bdB' h - cExp (comm C) (bHW bdB' h))) := by
      rw [← Finset.mul_sum]; ring
   _ = 2 * δ := by rw [hfubini]
 have hδ_nn : 0 ≤ δ := by
  rw [← hfubini]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt hB'_pos)) (sum_nonneg fun _ _ => hsSq_nonneg _)
 have hherm : ∀ h ∈ C, h.IsHermitian → ‖CLM h‖ ≤ 1 → hsSq (h - cExp B h) ≤ 2 * δ := by
  intro h hhC hhh hhnorm
  let s : Matrix (Fin d) (Fin d) ℂ := hhh.cfc (fun t => sqrt (max 0 (1 - t ^ 2)))
  have hsC : s ∈ C := cfc_mem_starSubalgebra hhh hhC _
  have hsh : sᴴ = s := (cfc_isHermitian hhh _).eq
  have hhs_comm : h * s = s * h := by
   conv_lhs => rw [← cfc_id hhh]
   conv_rhs => rw [← cfc_id hhh]
   dsimp only [s]; rw [cfc_mul, cfc_mul]; refine cfc_congr hhh fun i => mul_comm _ _
  have hh2s2 : h * h + s * s = 1 := by
   have hid : hhh.cfc (fun t => t) = h := cfc_id hhh
   dsimp only [s]
   conv_lhs => arg 1; rw [← hid]
   rw [cfc_mul, cfc_mul, cfc_add]
   have h1 : hhh.cfc (fun t => t * t + sqrt (max 0 (1 - t ^ 2)) * sqrt (max 0 (1 - t ^ 2))) =
     hhh.cfc (fun _ => 1) := by
    refine cfc_congr hhh fun i => ?_
    have hle : |hhh.eigenvalues i| ≤ 1 := (opNorm_isHermitian_eigenvalues_le hhh i).trans hhnorm
    have h1t : 0 ≤ 1 - hhh.eigenvalues i ^ 2 := by
     have : hhh.eigenvalues i ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (hhh.eigenvalues i)]
     linarith
    rw [max_eq_right h1t, mul_self_sqrt h1t]
    ring
   rw [h1, cfc_const hhh 1]; simp
  let v1 : Matrix (Fin d) (Fin d) ℂ := h + Complex.I • s
  let v2 : Matrix (Fin d) (Fin d) ℂ := h - Complex.I • s
  have hv1C : v1 ∈ C := C.add_mem hhC (C.smul_mem hsC Complex.I)
  have hv2C : v2 ∈ C := C.sub_mem hhC (C.smul_mem hsC Complex.I)
  have hv1U : v1 ∈ unitaryGroup (Fin d) ℂ := by
   rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
   dsimp only [v1]
   rw [conjTranspose_add, conjTranspose_smul, hhh.eq, hsh, star_def,
    Complex.conj_I, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul, Complex.I_mul_I,
    neg_neg, one_smul, hhs_comm]
   calc
    h * h + Complex.I • (s * h) + ((-Complex.I) • (s * h) + s * s)
     = h * h + s * s := by rw [neg_smul]; abel
    _ = 1 := hh2s2
  have hv2U : v2 ∈ unitaryGroup (Fin d) ℂ := by
   rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
   dsimp only [v2]
   rw [ctS, conjTranspose_smul, hhh.eq, hsh, star_def,
    Complex.conj_I, msm, mms, mms, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul, Complex.I_mul_I,
    neg_neg, one_smul, hhs_comm]
   calc
    h * h - Complex.I • (s * h) - ((-Complex.I) • (s * h) - s * s)
     = h * h + s * s := by rw [neg_smul]; abel
    _ = 1 := hh2s2
  have hh_eq : h = ((2 : ℂ)⁻¹) • (v1 + v2) := by
   dsimp only [v1, v2]
   have : h + Complex.I • s + (h - Complex.I • s) = (2 : ℂ) • h := by rw [two_smul]; abel
   rw [this, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
  have hdiff : h - cExp B h = ((2 : ℂ)⁻¹) • ((v1 - cExp B v1) + (v2 - cExp B v2)) := by
   conv_lhs => rw [hh_eq]
   rw [map_smul, map_add, ← smul_sub]
   congr 1; abel
  have hn : hsN (h - cExp B h) ≤ sqrt (2 * δ) := by
   rw [hdiff, hsNorm_smul]
   have hinv : ‖((2 : ℂ)⁻¹)‖ = (2 : ℝ)⁻¹ := by norm_num
   rw [hinv]
   have h1 : hsN (v1 - cExp B v1) ≤ sqrt (2 * δ) :=
    sqrt_le_sqrt (hunitary v1 hv1C hv1U)
   have h2 : hsN (v2 - cExp B v2) ≤ sqrt (2 * δ) :=
    sqrt_le_sqrt (hunitary v2 hv2C hv2U)
   have htri := hsN_add (v1 - cExp B v1) (v2 - cExp B v2)
   linarith
  have hsq := pow_le_pow_left₀ (hsN_nn _) hn 2
  rw [hsNorm_sq, sq_sqrt (by linarith)] at hsq
  exact hsq
 let h1 : Matrix (Fin d) (Fin d) ℂ := ((2 : ℂ)⁻¹) • (a + aᴴ)
 let h2 : Matrix (Fin d) (Fin d) ℂ := ((-Complex.I) / 2) • (a - aᴴ)
 have ha_star : aᴴ ∈ C := star_mem ha
 have hh1C : h1 ∈ C := C.smul_mem (C.add_mem ha ha_star) _
 have hh2C : h2 ∈ C := C.smul_mem (C.sub_mem ha ha_star) _
 have hh1h : h1.IsHermitian := by
  dsimp only [h1, IsHermitian]
  rw [conjTranspose_smul, conjTranspose_add, ctct,
   add_comm]
  congr 1; simp
 have hh2h : h2.IsHermitian := by
  dsimp only [h2, IsHermitian]
  rw [conjTranspose_smul, ctS, ctct]
  have hconj : star ((-Complex.I) / 2) = Complex.I / 2 := by
   rw [star_def, map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [hconj, ← neg_sub a aᴴ, smul_neg, ← neg_smul, ← neg_div]
 have hh1n : ‖CLM h1‖ ≤ 1 := by
  dsimp only [h1, CLM]
  rw [map_smul, map_add, norm_smul]
  have hinv : ‖((2 : ℂ)⁻¹)‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [hinv]
  have hst : ‖toEuclideanCLM (n := Fin d) (𝕜 := ℂ) aᴴ‖ =
    ‖toEuclideanCLM (n := Fin d) (𝕜 := ℂ) a‖ := opNorm_conjTranspose a
  have htri := norm_add_le (CLM a) (CLM aᴴ)
  dsimp only [CLM] at htri ha_norm
  linarith
 have hh2n : ‖CLM h2‖ ≤ 1 := by
  dsimp only [h2, CLM]
  rw [map_smul, map_sub, norm_smul]
  have hinv : ‖((-Complex.I) / 2)‖ = (2 : ℝ)⁻¹ := by
   rw [norm_div, norm_neg, Complex.norm_I]; norm_num
  rw [hinv]
  have hst : ‖toEuclideanCLM (n := Fin d) (𝕜 := ℂ) aᴴ‖ =
    ‖toEuclideanCLM (n := Fin d) (𝕜 := ℂ) a‖ := opNorm_conjTranspose a
  have htri := norm_sub_le (CLM a) (CLM aᴴ)
  dsimp only [CLM] at htri ha_norm
  linarith
 have ha_eq : a = h1 + Complex.I • h2 := by
  dsimp only [h1, h2]
  rw [smul_smul]
  have hc : Complex.I * (-Complex.I / 2) = (2 : ℂ)⁻¹ := by
   have : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
   rw [mul_div_assoc', this, one_div]
  rw [hc, ← smul_add]
  have hsum : a + aᴴ + (a - aᴴ) = (2 : ℂ) • a := by rw [two_smul]; abel
  rw [hsum, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
 have hdiff : a - cExp B a = (h1 - cExp B h1) + Complex.I • (h2 - cExp B h2) := by
  conv_lhs => rw [ha_eq]
  rw [map_add, LinearMap.map_smul (cExp B) Complex.I h2, smul_sub]
  abel
 rw [hdiff]
 calc
  hsSq ((h1 - cExp B h1) + Complex.I • (h2 - cExp B h2))
   ≤ 2 * hsSq (h1 - cExp B h1) + 2 * hsSq (Complex.I • (h2 - cExp B h2)) :=
     hsSq_add_le _ _
  _ = 2 * hsSq (h1 - cExp B h1) + 2 * hsSq (h2 - cExp B h2) := by
     rw [hsSq_smul, Complex.norm_I, one_pow, one_mul]
  _ ≤ 2 * (2 * δ) + 2 * (2 * δ) := by
     gcongr
     · exact hherm h1 hh1C hh1h hh1n
     · exact hherm h2 hh2C hh2h hh2n
  _ = 8 * δ := by ring
end ReverseScaleEstimate
/- ### 6b. Bratteli correction for near-inclusions (Lemma 3.1 of Thom) -/
section BratteliCorrection
lemma norm_trace_conjTranspose_mul_le {m n : Type*} [Fintype m] [Fintype n]
  (A B : Matrix m n ℂ) : ‖(Aᴴ * B).trace‖ ≤ hsN A * hsN B := by
 rw [← inner_matToEucl]
 have hcs := @norm_inner_le_norm ℂ (EuclideanSpace ℂ (m × n)) _ _ _ (m2e A) (m2e B)
 rwa [norm_matToEucl, norm_matToEucl] at hcs
lemma sum_hsSq_centralProj_sub_condExp_le {d : ℕ}
  {B A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} (bdB : BDec B)
  {ε : ℝ} (hinc : ∀ b ∈ B, ‖CLM b‖ ≤ 1 → hsSq (b - cExp A b) ≤ ε ^ 2 * (d : ℝ)) :
  ∑ i : Fin bdB.t, hsSq (cPr bdB i - cExp A (cPr bdB i)) ≤ ε ^ 2 * (d : ℝ) := by
 classical
 let sgn : Bool → ℂ := fun b => if b then 1 else -1
 let e : Fin bdB.t → Matrix (Fin d) (Fin d) ℂ := fun i => cPr bdB i - cExp A (cPr bdB i)
 have hunit : ∀ σ : Fin bdB.t → Bool,
   (∑ i : Fin bdB.t, sgn (σ i) • cPr bdB i) ∈ unitaryGroup (Fin d) ℂ := by
  intro σ
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_sum,
   Finset.sum_mul]
  have hterm : ∀ i : Fin bdB.t,
    (sgn (σ i) • cPr bdB i)ᴴ * (∑ j : Fin bdB.t, sgn (σ j) • cPr bdB j) =
     cPr bdB i := by
   intro i
   rw [Finset.mul_sum, sum_eq_single i]
   ·
    rw [conjTranspose_smul, cPr_herm, Matrix.smul_mul, Matrix.mul_smul,
     smul_smul, cPr_mul, if_pos rfl]
    have hs : star (sgn (σ i)) * sgn (σ i) = 1 := by cases σ i <;> simp [sgn]
    rw [hs, one_smul]
   ·
    intro j _ hji
    rw [conjTranspose_smul, cPr_herm, Matrix.smul_mul, Matrix.mul_smul,
     cPr_mul, if_neg hji.symm, smul_zero, smul_zero]
   · intro h; exact absurd (mem_univ i) h
  simp_rw [hterm]
  exact sum_cPr bdB
 have hmem : ∀ σ : Fin bdB.t → Bool, (∑ i : Fin bdB.t, sgn (σ i) • cPr bdB i) ∈ B :=
  fun σ => B.sum_mem fun i _ => B.smul_mem (cPr_mem bdB i) _
 have hbound : ∀ σ : Fin bdB.t → Bool,
   hsSq (∑ i : Fin bdB.t, sgn (σ i) • e i) ≤ ε ^ 2 * (d : ℝ) := by
  intro σ
  have heq : (∑ i : Fin bdB.t, sgn (σ i) • cPr bdB i) -
    cExp A (∑ i : Fin bdB.t, sgn (σ i) • cPr bdB i) =
    ∑ i : Fin bdB.t, sgn (σ i) • e i := by
   rw [map_sum, ← sum_sub_distrib]
   refine sum_congr rfl fun i _ => ?_
   rw [LinearMap.map_smul, ← smul_sub]
  rw [← heq]
  exact hinc _ (hmem σ) (opNorm_unitary_le' (hunit σ))
 have hexpand : ∀ σ : Fin bdB.t → Bool,
   hsSq (∑ i : Fin bdB.t, sgn (σ i) • e i) =
    ∑ i : Fin bdB.t, ∑ j : Fin bdB.t,
     (star (sgn (σ i)) * sgn (σ j) * ((e i)ᴴ * e j).trace).re := by
  intro σ
  rw [hsSq_tr, conjTranspose_sum, Finset.sum_mul, trace_sum, re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, trace_sum, re_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
   trace_smul, smul_eq_mul]
 have hsum_sig : ∑ σ : Fin bdB.t → Bool, hsSq (∑ i : Fin bdB.t, sgn (σ i) • e i) =
   (Fintype.card (Fin bdB.t → Bool) : ℝ) * ∑ i : Fin bdB.t, hsSq (e i) := by
  simp_rw [hexpand]
  rw [sum_comm]
  rw [Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm, sum_eq_single i]
  ·
   have h1 : ∀ σ : Fin bdB.t → Bool,
     (star (sgn (σ i)) * sgn (σ i) * ((e i)ᴴ * e i).trace).re = hsSq (e i) := by
    intro σ
    have hs : star (sgn (σ i)) * sgn (σ i) = 1 := by cases σ i <;> simp [sgn]
    rw [hs, one_mul, ← hsSq_tr]
   simp_rw [h1, sum_const, card_univ, nsmul_eq_mul]
  ·
   intro j _ hji
   rw [← re_sum, ← Finset.sum_mul]
   have hzero : ∑ σ : Fin bdB.t → Bool, star (sgn (σ i)) * sgn (σ j) = 0 := by
    let flip : (Fin bdB.t → Bool) → (Fin bdB.t → Bool) := fun σ => Function.update σ i (!(σ i))
    have hinv : Function.Involutive flip := by
     intro σ; funext k
     by_cases h : k = i
     · subst h; simp [flip]
     · simp [flip, h]
    have hneg : ∀ σ : Fin bdB.t → Bool,
      star (sgn (flip σ i)) * sgn (flip σ j) = -(star (sgn (σ i)) * sgn (σ j)) := by
     intro σ
     have hfi : flip σ i = !(σ i) := by simp [flip]
     have hfj : flip σ j = σ j := by simp [flip, hji]
     rw [hfi, hfj]
     cases σ i <;> cases σ j <;> simp [sgn]
    have hsum_eq : ∑ σ : Fin bdB.t → Bool, star (sgn (flip σ i)) * sgn (flip σ j) =
      ∑ σ : Fin bdB.t → Bool, star (sgn (σ i)) * sgn (σ j) :=
     Fintype.sum_bijective flip hinv.bijective _ _ fun _ => rfl
    simp_rw [hneg, Finset.sum_neg_distrib] at hsum_eq
    have h2 : (2 : ℂ) * ∑ σ : Fin bdB.t → Bool, star (sgn (σ i)) * sgn (σ j) = 0 := by
     linear_combination -hsum_eq
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
   rw [hzero, zero_mul, zero_re]
  · intro h; exact absurd (mem_univ i) h
 have hle : ∑ σ : Fin bdB.t → Bool, hsSq (∑ i : Fin bdB.t, sgn (σ i) • e i) ≤
   (Fintype.card (Fin bdB.t → Bool) : ℝ) * (ε ^ 2 * (d : ℝ)) := by
  calc
   ∑ σ : Fin bdB.t → Bool, hsSq (∑ i : Fin bdB.t, sgn (σ i) • e i)
    ≤ ∑ _σ : Fin bdB.t → Bool, (ε ^ 2 * (d : ℝ)) := sum_le_sum fun σ _ => hbound σ
   _ = (Fintype.card (Fin bdB.t → Bool) : ℝ) * (ε ^ 2 * (d : ℝ)) := by
      rw [sum_const, card_univ, nsmul_eq_mul]
 rw [hsum_sig] at hle
 have hcard_pos : (0 : ℝ) < (Fintype.card (Fin bdB.t → Bool) : ℝ) := by
  rw [Fintype.card_fun, Fintype.card_bool, card_fin]
  positivity
 exact le_of_mul_le_mul_left hle hcard_pos
structure BCData {d : ℕ}
  {B A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdB : BDec B) (bdA : BDec A) (ε : ℝ) where
 m : ℕ
 Bhat : StarSubalgebra ℂ (Matrix (Fin m) (Fin m) ℂ)
 Ahat : StarSubalgebra ℂ (Matrix (Fin m) (Fin m) ℂ)
 hBAhat : Bhat ≤ Ahat
 q' : Fin bdB.t → ℕ
 r' : Fin bdA.t → ℕ
 bdBhat : BDec Bhat
 bdAhat : BDec Ahat
 eB : Fin bdBhat.t ≃ {i : Fin bdB.t // 0 < q' i}
 eA : Fin bdAhat.t ≃ {j : Fin bdA.t // 0 < r' j}
 πB : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin m) (Fin m) ℂ
 πA' : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin m) (Fin m) ℂ
 W : Matrix (Fin m) (Fin d) ℂ
 hm_diff : |(m : ℝ) - (d : ℝ)| ≤ 2 * ε ^ 2 * (d : ℝ)
 hB_mult : ∑ i : Fin bdB.t, (bdB.r i : ℝ) * |(q' i : ℝ) - (bdB.s i : ℝ)| ≤ 8 * ε ^ 2 * (d : ℝ)
 hA_mult : ∑ j : Fin bdA.t, (bdA.s j : ℝ) * |(r' j : ℝ) - (bdA.r j : ℝ)| ≤ 6 * ε ^ 2 * (d : ℝ)
 hBhat_mem : ∀ bhat, bhat ∈ Bhat ↔ ∃ b ∈ B, πB b = bhat
 hBhat_r : ∀ i', bdBhat.r i' = bdB.r (eB i').1
 hBhat_s : ∀ i', bdBhat.s i' = q' (eB i').1
 hBhat_z : ∀ i', cPr bdBhat i' = πB (cPr bdB (eB i').1)
 hBhat_tr : ∀ i, (πB (cPr bdB i)).trace = ((bdB.r i * q' i : ℕ) : ℂ)
 hBhat_zero : ∀ i, q' i = 0 → πB (cPr bdB i) = 0
 hBhat_lift : ∀ bhat ∈ Bhat, ∃ b ∈ B, ‖CLM b‖ ≤ ‖CLM bhat‖ ∧ πB b = bhat
 hAhat_mem : ∀ x, x ∈ Ahat ↔ ∀ c ∈ comm A, x * πA' c = πA' c * x
 hAhat_r : ∀ j', bdAhat.r j' = r' (eA j').1
 hAhat_s : ∀ j', bdAhat.s j' = bdA.s (eA j').1
 hAhat_z : ∀ j', cPr bdAhat j' = πA' (cPr bdA (eA j').1)
 hAhat_tr : ∀ j, (πA' (cPr bdA j)).trace = ((r' j * bdA.s j : ℕ) : ℂ)
 hAhat_zero : ∀ j, r' j = 0 → πA' (cPr bdA j) = 0
 hπB_one : πB 1 = 1
 hπB_add : ∀ x y, πB (x + y) = πB x + πB y
 hπB_smul : ∀ (α : ℂ) x, πB (α • x) = α • πB x
 hπB_mul : ∀ x y, x ∈ B → y ∈ B → πB (x * y) = πB x * πB y
 hπB_star : ∀ x, πB xᴴ = (πB x)ᴴ
 hπB_opNorm : ∀ x, ‖CLM (πB x)‖ ≤ ‖CLM x‖
 hπA'_one : πA' 1 = 1
 hπA'_add : ∀ c₁ c₂, πA' (c₁ + c₂) = πA' c₁ + πA' c₂
 hπA'_smul : ∀ (α : ℂ) c, πA' (α • c) = α • πA' c
 hπA'_mul : ∀ c₁ c₂, c₁ ∈ comm A → c₂ ∈ comm A → πA' (c₁ * c₂) = πA' c₁ * πA' c₂
 hπA'_star : ∀ c, πA' cᴴ = (πA' c)ᴴ
 hπ_comm : ∀ b ∈ B, ∀ c ∈ comm A, πB b * πA' c = πA' c * πB b
 hW_src : (Wᴴ * W) * (Wᴴ * W) = Wᴴ * W
 hW_tgt : (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ
 hW_src_tr : ((1 - Wᴴ * W).trace).re ≤ 2 * ε ^ 2 * (d : ℝ)
 hW_tgt_tr : ((1 - W * Wᴴ).trace).re ≤ 4 * ε ^ 2 * (d : ℝ)
 hW_comm_A' : ∀ c ∈ comm A, πA' c * W = W * c
 hW_comm_AB : ∀ x ∈ A, x ∈ B → πB x * W = W * x
 hW_approx_B : ∀ b ∈ B, ‖CLM b‖ ≤ 1 → hsN (πB b * W - W * b) ≤ 6 * ε * sqrt (d : ℝ)
 hW_conj_A : ∀ a ∈ A, W * a * Wᴴ ∈ Ahat
 hW_conj_Ahat : ∀ ahat ∈ Ahat, Wᴴ * ahat * W ∈ A
lemma proj_inner_eq_norm_sq {K : Type*} [Fintype K] [DecidableEq K]
  {P : Matrix K K ℂ} (hPh : P.IsHermitian) (hPp : P * P = P) (v : EuclideanSpace ℂ K) :
  ⟪v, CLM P v⟫_ℂ = ((‖CLM P v‖ ^ 2 : ℝ) : ℂ) := by
 have hcomp : CLM P v = CLM P (CLM P v) := by
  have : CLM (P * P) v = CLM P (CLM P v) := by dsimp only [CLM]; rw [map_mul]; rfl
  rw [← this, hPp]
 calc
  ⟪v, CLM P v⟫_ℂ
   = ⟪v, ContinuousLinearMap.adjoint (CLM P) (CLM P v)⟫_ℂ := by
     rw [toCLM_adjoint, hPh.eq, ← hcomp]
  _ = ⟪CLM P v, CLM P v⟫_ℂ := ContinuousLinearMap.adjoint_inner_right _ _ _
  _ = ((‖CLM P v‖ ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K]; simp
lemma proj_norm_sq_le {K : Type*} [Fintype K] [DecidableEq K]
  {P : Matrix K K ℂ} (hPh : P.IsHermitian) (hPp : P * P = P) (v : EuclideanSpace ℂ K) :
  ‖CLM P v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
 have hself := proj_inner_eq_norm_sq hPh hPp v
 have hsym : ⟪CLM P v, v⟫_ℂ = ((‖CLM P v‖ ^ 2 : ℝ) : ℂ) := by
  have := congrArg (starRingEnd ℂ) hself
  rw [inner_conj_symm] at this
  simpa using this
 have hpyth : ‖CLM P v‖ ^ 2 + ‖v - CLM P v‖ ^ 2 = ‖v‖ ^ 2 := by
  have hC : ((‖CLM P v‖ ^ 2 + ‖v - CLM P v‖ ^ 2 : ℝ) : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
   rw [Complex.ofReal_add,
    show ((‖v - CLM P v‖ ^ 2 : ℝ) : ℂ) = ⟪v - CLM P v, v - CLM P v⟫_ℂ by
     rw [inner_self_eq_norm_sq_to_K]; simp,
    show ((‖v‖ ^ 2 : ℝ) : ℂ) = ⟪v, v⟫_ℂ by rw [inner_self_eq_norm_sq_to_K]; simp,
    inner_sub_left, inner_sub_right, inner_sub_right, hself, hsym,
    show ⟪CLM P v, CLM P v⟫_ℂ = ((‖CLM P v‖ ^ 2 : ℝ) : ℂ) by
     rw [inner_self_eq_norm_sq_to_K]; simp]
   ring
  exact_mod_cast hC
 linarith [sq_nonneg ‖v - CLM P v‖]
abbrev DilK {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) : Type :=
 Σ j : Fin bdA.t, Fin d × Fin (bdA.s j) × Fin (bdA.s j)
def dRB {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (b : Matrix (Fin d) (Fin d) ℂ) : Matrix (DilK bdA) (DilK bdA) ℂ :=
 Matrix.of fun ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩ =>
  if h : j₁ = j₂ then if k₁ = h ▸ k₂ ∧ l₁ = h ▸ l₂ then b x₁ x₂ else 0 else 0
def dilRhoA' {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (c : Matrix (Fin d) (Fin d) ℂ) : Matrix (DilK bdA) (DilK bdA) ℂ :=
 Matrix.of fun ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩ =>
  if h : j₁ = j₂ then if x₁ = x₂ ∧ k₁ = h ▸ k₂ then cBlk bdA c j₁ l₁ (h ▸ l₂) else 0 else 0
def dV {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) : Matrix (DilK bdA) (Fin d) ℂ :=
 Matrix.of fun ⟨j, x, k, l⟩ y =>
  ((sqrt (bdA.s j : ℝ) : ℂ)⁻¹) *
   ∑ a : Fin (bdA.r j), bdA.U x ⟨j, a, k⟩ * bdA.Uᴴ ⟨j, a, l⟩ y
lemma dilRhoB_one {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) : dRB bdA 1 = 1 := by
 ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩
 rw [Matrix.one_apply]
 dsimp only [dRB, of_apply]
 by_cases hj : j₁ = j₂
 ·
  subst hj
  simp only [↓reduceDIte, Matrix.one_apply, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and]
  by_cases hkl : k₁ = k₂ ∧ l₁ = l₂
  · rcases hkl with ⟨rfl, rfl⟩; simp
  · simp [hkl]
 · simp [hj]
lemma dilRhoB_add {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (b₁ b₂ : Matrix (Fin d) (Fin d) ℂ) :
  dRB bdA (b₁ + b₂) = dRB bdA b₁ + dRB bdA b₂ := by
 ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩
 rw [Matrix.add_apply]
 dsimp only [dRB, of_apply]
 by_cases hj : j₁ = j₂
 · subst hj; simp only [↓reduceDIte, Matrix.add_apply]; split_ifs <;> simp
 · simp [hj]
lemma dilRhoB_smul {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (α : ℂ) (b : Matrix (Fin d) (Fin d) ℂ) :
  dRB bdA (α • b) = α • dRB bdA b := by
 ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩
 rw [Matrix.smul_apply]
 dsimp only [dRB, of_apply]
 by_cases hj : j₁ = j₂
 · subst hj; simp only [↓reduceDIte, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
 · simp [hj]
lemma dilRhoB_star {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (b : Matrix (Fin d) (Fin d) ℂ) :
  dRB bdA bᴴ = (dRB bdA b)ᴴ := by
 ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩
 rw [ctA]
 dsimp only [dRB, of_apply]
 by_cases hj : j₁ = j₂
 ·
  subst hj
  simp only [↓reduceDIte, ctA]
  by_cases hkl : k₁ = k₂ ∧ l₁ = l₂
  · rcases hkl with ⟨rfl, rfl⟩; simp
  ·
   have hkl' : ¬(k₂ = k₁ ∧ l₂ = l₁) := fun ⟨hk, hl⟩ => hkl ⟨hk.symm, hl.symm⟩
   rw [if_neg hkl, if_neg hkl', star_zero]
 · rw [dif_neg hj, dif_neg (Ne.symm hj), star_zero]
lemma dilRhoB_mul {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (b₁ b₂ : Matrix (Fin d) (Fin d) ℂ) :
  dRB bdA (b₁ * b₂) = dRB bdA b₁ * dRB bdA b₂ := by
 ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩
 rw [mul_apply, Fintype.sum_sigma, sum_eq_single j₁]
 ·
  simp only [dRB, of_apply, ↓reduceDIte, sum_prod_type]
  by_cases hj : j₁ = j₂
  ·
   subst hj
   simp only [↓reduceDIte]
   by_cases hkl : k₁ = k₂ ∧ l₁ = l₂
   ·
    rcases hkl with ⟨rfl, rfl⟩
    simp only [and_self, ↓reduceIte, mul_apply]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_eq_single k₁]
    ·
     rw [sum_eq_single l₁]
     · simp
     · intro l _ hl; simp [Ne.symm hl]
     · intro h; exact absurd (mem_univ l₁) h
    · intro k _ hk; exact sum_eq_zero fun l _ => by simp [Ne.symm hk]
    · intro h; exact absurd (mem_univ k₁) h
   ·
    rw [if_neg hkl]
    refine (sum_eq_zero fun x _ => sum_eq_zero fun k _ =>
     sum_eq_zero fun l _ => ?_).symm
    by_cases h1 : k₁ = k ∧ l₁ = l
    · rcases h1 with ⟨rfl, rfl⟩; simp [hkl]
    · simp [h1]
  ·
   simp only [dif_neg hj]
   exact (sum_eq_zero fun x _ => sum_eq_zero fun k _ =>
    sum_eq_zero fun l _ => by simp).symm
 · intro j _ hji; exact sum_eq_zero fun p _ => by simp [dRB, Ne.symm hji]
 · intro h; exact absurd (mem_univ j₁) h
lemma dilRhoB_opNorm {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (b : Matrix (Fin d) (Fin d) ℂ) :
  ‖CLM (dRB bdA b)‖ ≤ ‖CLM b‖ := by
 refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
 have hsq : ‖CLM (dRB bdA b) v‖ ^ 2 ≤ (‖CLM b‖ * ‖v‖) ^ 2 := by
  rw [mul_pow, norm_sq_eq, norm_sq_eq, Fintype.sum_sigma,
   Fintype.sum_sigma, Finset.mul_sum]
  refine sum_le_sum fun j _ => ?_
  rw [sum_prod_type, sum_prod_type, sum_comm,
   sum_comm (f := fun x p => ‖v.ofLp ⟨j, x, p⟩‖ ^ 2), Finset.mul_sum]
  refine sum_le_sum fun p _ => ?_
  let w : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 fun x => v.ofLp ⟨j, x, p⟩
  have hact : ∀ x : Fin d, (CLM (dRB bdA b) v).ofLp ⟨j, x, p⟩ = (CLM b w).ofLp x := by
   intro x
   dsimp only [CLM]
   rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, mulVec, mulVec,
    dotProduct, dotProduct, Fintype.sum_sigma, sum_eq_single j]
   ·
    simp only [dRB, of_apply, ↓reduceDIte, sum_prod_type]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_eq_single p.1]
    ·
     rw [sum_eq_single p.2]
     · simp [w]
     · intro l _ hl; simp [Ne.symm hl]
     · intro h; exact absurd (mem_univ p.2) h
    · intro k _ hk; exact sum_eq_zero fun l _ => by simp [Ne.symm hk]
    · intro h; exact absurd (mem_univ p.1) h
   · intro j' _ hj'; exact sum_eq_zero fun q _ => by simp [dRB, Ne.symm hj']
   · intro h; exact absurd (mem_univ j) h
  simp_rw [hact]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) ((CLM b).le_opNorm w) 2
  rwa [mul_pow, norm_sq_eq, norm_sq_eq] at h1
 nlinarith [norm_nonneg (CLM (dRB bdA b) v), mul_nonneg (norm_nonneg (CLM b)) (norm_nonneg v)]
lemma dilRhoA'_one {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) : dilRhoA' bdA 1 = 1 := by
 ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩
 rw [Matrix.one_apply]
 dsimp only [dilRhoA', of_apply]
 by_cases hj : j₁ = j₂
 ·
  subst hj
  simp only [↓reduceDIte, commBlock_one, Matrix.one_apply, Sigma.mk.inj_iff, heq_eq_eq,
   Prod.mk.injEq, true_and]
  by_cases hxk : x₁ = x₂ ∧ k₁ = k₂
  · rcases hxk with ⟨rfl, rfl⟩; simp
  · rw [if_neg hxk, if_neg (fun ⟨hx, hk, _⟩ => hxk ⟨hx, hk⟩)]
 · simp [hj]
lemma dilRhoA'_add {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (c₁ c₂ : Matrix (Fin d) (Fin d) ℂ) :
  dilRhoA' bdA (c₁ + c₂) = dilRhoA' bdA c₁ + dilRhoA' bdA c₂ := by
 ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩
 rw [Matrix.add_apply]
 dsimp only [dilRhoA', of_apply]
 by_cases hj : j₁ = j₂
 · subst hj; simp only [↓reduceDIte, commBlock_add, Matrix.add_apply]; split_ifs <;> simp
 · simp [hj]
lemma dilRhoA'_smul {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (α : ℂ) (c : Matrix (Fin d) (Fin d) ℂ) :
  dilRhoA' bdA (α • c) = α • dilRhoA' bdA c := by
 ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩
 rw [Matrix.smul_apply]
 dsimp only [dilRhoA', of_apply]
 by_cases hj : j₁ = j₂
 · subst hj; simp only [↓reduceDIte, commBlock_smul, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
 · simp [hj]
lemma dilRhoA'_star {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (c : Matrix (Fin d) (Fin d) ℂ) :
  dilRhoA' bdA cᴴ = (dilRhoA' bdA c)ᴴ := by
 ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩
 rw [ctA]
 dsimp only [dilRhoA', of_apply]
 by_cases hj : j₁ = j₂
 ·
  subst hj
  simp only [↓reduceDIte, commBlock_conjTranspose, ctA]
  by_cases hxk : x₁ = x₂ ∧ k₁ = k₂
  · rcases hxk with ⟨rfl, rfl⟩; simp
  ·
   have hxk' : ¬(x₂ = x₁ ∧ k₂ = k₁) := fun ⟨hx, hk⟩ => hxk ⟨hx.symm, hk.symm⟩
   rw [if_neg hxk, if_neg hxk', star_zero]
 · rw [dif_neg hj, dif_neg (Ne.symm hj), star_zero]
lemma dilRhoA'_mul {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) {c₁ c₂ : Matrix (Fin d) (Fin d) ℂ}
  (hc₁ : c₁ ∈ comm A) (hc₂ : c₂ ∈ comm A) :
  dilRhoA' bdA (c₁ * c₂) = dilRhoA' bdA c₁ * dilRhoA' bdA c₂ := by
 ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩
 rw [mul_apply, Fintype.sum_sigma, sum_eq_single j₁]
 ·
  simp only [dilRhoA', of_apply, ↓reduceDIte, commBlock_mul bdA hc₁ hc₂, sum_prod_type]
  by_cases hj : j₁ = j₂
  ·
   subst hj
   simp only [↓reduceDIte]
   by_cases hxk : x₁ = x₂ ∧ k₁ = k₂
   ·
    rcases hxk with ⟨rfl, rfl⟩
    simp only [and_self, ↓reduceIte]
    symm
    rw [sum_eq_single x₁]
    ·
     rw [sum_eq_single k₁]
     · simp [mul_apply]
     · intro k _ hk; exact sum_eq_zero fun l _ => by simp [Ne.symm hk]
     · intro h; exact absurd (mem_univ k₁) h
    ·
     intro x _ hx; exact sum_eq_zero fun k _ => sum_eq_zero fun l _ => by
      simp [Ne.symm hx]
    · intro h; exact absurd (mem_univ x₁) h
   ·
    rw [if_neg hxk]
    refine (sum_eq_zero fun x _ => sum_eq_zero fun k _ =>
     sum_eq_zero fun l _ => ?_).symm
    by_cases h1 : x₁ = x ∧ k₁ = k
    · rcases h1 with ⟨rfl, rfl⟩; simp [hxk]
    · simp [h1]
  ·
   simp only [dif_neg hj]
   exact (sum_eq_zero fun x _ => sum_eq_zero fun k _ =>
    sum_eq_zero fun l _ => by simp).symm
 · intro j _ hji; exact sum_eq_zero fun p _ => by simp [dilRhoA', Ne.symm hji]
 · intro h; exact absurd (mem_univ j₁) h
lemma dilRho_comm {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (b c : Matrix (Fin d) (Fin d) ℂ) :
  dRB bdA b * dilRhoA' bdA c = dilRhoA' bdA c * dRB bdA b := by
 ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩
 rw [mul_apply, mul_apply, Fintype.sum_sigma, Fintype.sum_sigma,
  sum_eq_single j₁, sum_eq_single j₁]
 ·
  simp only [dRB, dilRhoA', of_apply, ↓reduceDIte, sum_prod_type]
  by_cases hj : j₁ = j₂
  ·
   subst hj
   simp only [↓reduceDIte]
   have hL : ∑ x : Fin d, ∑ k : Fin (bdA.s j₁), ∑ l : Fin (bdA.s j₁),
     (if k₁ = k ∧ l₁ = l then b x₁ x else 0) *
      (if x = x₂ ∧ k = k₂ then cBlk bdA c j₁ l l₂ else 0) =
     if k₁ = k₂ then b x₁ x₂ * cBlk bdA c j₁ l₁ l₂ else 0 := by
    rw [sum_eq_single x₂]
    ·
     rw [sum_eq_single k₁]
     ·
      rw [sum_eq_single l₁]
      · by_cases hk : k₁ = k₂ <;> simp [hk]
      · intro l _ hl; simp [Ne.symm hl]
      · intro h; exact absurd (mem_univ l₁) h
     · intro k _ hk; exact sum_eq_zero fun l _ => by simp [Ne.symm hk]
     · intro h; exact absurd (mem_univ k₁) h
    ·
     intro x _ hx; exact sum_eq_zero fun k _ => sum_eq_zero fun l _ => by
      simp [hx]
    · intro h; exact absurd (mem_univ x₂) h
   have hR : ∑ x : Fin d, ∑ k : Fin (bdA.s j₁), ∑ l : Fin (bdA.s j₁),
     (if x₁ = x ∧ k₁ = k then cBlk bdA c j₁ l₁ l else 0) *
      (if k = k₂ ∧ l = l₂ then b x x₂ else 0) =
     if k₁ = k₂ then cBlk bdA c j₁ l₁ l₂ * b x₁ x₂ else 0 := by
    rw [sum_eq_single x₁]
    ·
     rw [sum_eq_single k₁]
     ·
      rw [sum_eq_single l₂]
      · by_cases hk : k₁ = k₂ <;> simp [hk]
      · intro l _ hl; simp [hl]
      · intro h; exact absurd (mem_univ l₂) h
     · intro k _ hk; exact sum_eq_zero fun l _ => by simp [Ne.symm hk]
     · intro h; exact absurd (mem_univ k₁) h
    ·
     intro x _ hx; exact sum_eq_zero fun k _ => sum_eq_zero fun l _ => by
      simp [Ne.symm hx]
    · intro h; exact absurd (mem_univ x₁) h
   rw [hL, hR]; by_cases hk : k₁ = k₂ <;> simp [hk, mul_comm]
  · simp only [dif_neg hj, mul_zero, sum_const_zero]
 · intro j _ hji; exact sum_eq_zero fun p _ => by simp [dilRhoA', Ne.symm hji]
 · intro h; exact absurd (mem_univ j₁) h
 · intro j _ hji; exact sum_eq_zero fun p _ => by simp [dRB, Ne.symm hji]
 · intro h; exact absurd (mem_univ j₁) h
lemma dilV_mul_U {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (j : Fin bdA.t) (x : Fin d) (k l : Fin (bdA.s j))
  (j' : Fin bdA.t) (a' : Fin (bdA.r j')) (l' : Fin (bdA.s j')) :
  (dV bdA * bdA.U) ⟨j, x, k, l⟩ ⟨j', a', l'⟩ =
   if h : j = j' then if l = h ▸ l' then
    ((sqrt (bdA.s j : ℝ) : ℂ)⁻¹) * bdA.U x ⟨j, h ▸ a', k⟩ else 0 else 0 := by
 rw [mul_apply]
 dsimp only [dV, of_apply]
 simp_rw [mul_assoc, ← Finset.mul_sum]
 have hsum : ∑ y : Fin d, (∑ a : Fin (bdA.r j), bdA.U x ⟨j, a, k⟩ * bdA.Uᴴ ⟨j, a, l⟩ y) *
   bdA.U y ⟨j', a', l'⟩ =
   ∑ a : Fin (bdA.r j), bdA.U x ⟨j, a, k⟩ * (bdA.Uᴴ * bdA.U) ⟨j, a, l⟩ ⟨j', a', l'⟩ := by
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => by rw [← Finset.mul_sum, ← mul_apply]
 rw [hsum, bdA.U_star_mul]
 by_cases hj : j = j'
 ·
  subst hj
  simp only [↓reduceDIte, Matrix.one_apply, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and]
  by_cases hl : l = l'
  ·
   subst hl
   simp only [and_true, ↓reduceIte]
   rw [sum_eq_single a']
   · simp
   · intro a _ ha; simp [ha]
   · intro h; exact absurd (mem_univ a') h
  · simp [hl]
 · simp [hj]
lemma dilV_star_mul {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) : (dV bdA)ᴴ * dV bdA = 1 := by
 have h1 : (dV bdA * bdA.U)ᴴ * (dV bdA * bdA.U) = 1 := by
  ext ⟨j₁, a₁, l₁⟩ ⟨j₂, a₂, l₂⟩
  rw [mul_apply, Fintype.sum_sigma]
  by_cases hj : j₁ = j₂
  ·
   subst hj
   rw [sum_eq_single j₁]
   ·
    simp only [ctA, sum_prod_type]
    have hterm : ∀ (x : Fin d) (k l : Fin (bdA.s j₁)),
      star ((dV bdA * bdA.U) ⟨j₁, x, k, l⟩ ⟨j₁, a₁, l₁⟩) *
       (dV bdA * bdA.U) ⟨j₁, x, k, l⟩ ⟨j₁, a₂, l₂⟩ =
      if l = l₁ ∧ l = l₂ then
       ((bdA.s j₁ : ℂ)⁻¹) * (bdA.Uᴴ ⟨j₁, a₁, k⟩ x * bdA.U x ⟨j₁, a₂, k⟩) else 0 := by
     intro x k l
     rw [dilV_mul_U, dilV_mul_U]
     simp only [↓reduceDIte]
     by_cases h1 : l = l₁ ∧ l = l₂
     ·
      rcases h1 with ⟨rfl, hll⟩
      simp only [↓reduceIte, hll, and_self]
      have hsq : star ((sqrt (bdA.s j₁ : ℝ) : ℂ)⁻¹) *
        ((sqrt (bdA.s j₁ : ℝ) : ℂ)⁻¹) = (bdA.s j₁ : ℂ)⁻¹ := by
       rw [star_inv₀, star_def, conj_ofReal, ← mul_inv,
        ← ofReal_mul, mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
      rw [star_mul, ctA]
      linear_combination (star (bdA.U x ⟨j₁, a₁, k⟩) * bdA.U x ⟨j₁, a₂, k⟩) * hsq
     ·
      by_cases hl1 : l = l₁
      ·
       subst hl1
       have hl2 : l ≠ l₂ := fun h => h1 ⟨rfl, h⟩
       simp [hl2]
      · simp [hl1]
    simp_rw [hterm]
    by_cases hl : l₁ = l₂
    ·
     subst hl
     have hcol : ∀ (x : Fin d) (k : Fin (bdA.s j₁)),
       ∑ l : Fin (bdA.s j₁), (if l = l₁ ∧ l = l₁ then
        (bdA.s j₁ : ℂ)⁻¹ * (bdA.Uᴴ ⟨j₁, a₁, k⟩ x * bdA.U x ⟨j₁, a₂, k⟩) else 0) =
       (bdA.s j₁ : ℂ)⁻¹ * (bdA.Uᴴ ⟨j₁, a₁, k⟩ x * bdA.U x ⟨j₁, a₂, k⟩) := by
      intro x k
      rw [sum_eq_single l₁]
      · simp
      · intro l _ hll; simp [hll]
      · intro h; exact absurd (mem_univ l₁) h
     simp_rw [hcol]
     rw [sum_comm]
     have hk : ∀ k : Fin (bdA.s j₁),
       ∑ x : Fin d, (bdA.s j₁ : ℂ)⁻¹ * (bdA.Uᴴ ⟨j₁, a₁, k⟩ x * bdA.U x ⟨j₁, a₂, k⟩) =
       (bdA.s j₁ : ℂ)⁻¹ * (if a₁ = a₂ then 1 else 0) := by
      intro k
      rw [← Finset.mul_sum, ← mul_apply, bdA.U_star_mul]
      simp [Matrix.one_apply]
     simp_rw [hk, sum_const, card_univ, card_fin, nsmul_eq_mul,
      ← mul_assoc]
     have hs0 : (bdA.s j₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (bdA.hs j₁))
     rw [mul_inv_cancel₀ hs0, one_mul, Matrix.one_apply]
     simp
    ·
     rw [Matrix.one_apply_ne (by intro h; cases h; exact hl rfl)]
     refine sum_eq_zero fun x _ => sum_eq_zero fun k _ =>
      sum_eq_zero fun l _ => ?_
     rw [if_neg (fun ⟨h1, h2⟩ => hl (h1.symm.trans h2))]
   ·
    intro j _ hjj
    refine sum_eq_zero fun p _ => ?_
    rw [ctA, dilV_mul_U, dif_neg hjj, star_zero, zero_mul]
   · intro h; exact absurd (mem_univ j₁) h
  ·
   rw [Matrix.one_apply_ne (by intro h; cases h; exact hj rfl)]
   refine sum_eq_zero fun j _ => sum_eq_zero fun p _ => ?_
   rw [ctA, dilV_mul_U, dilV_mul_U]
   by_cases h1 : j = j₁
   · subst h1; simp [hj]
   · simp [h1]
 calc
  (dV bdA)ᴴ * dV bdA = bdA.U * (bdA.Uᴴ * ((dV bdA)ᴴ * dV bdA) * bdA.U) * bdA.Uᴴ := by
     calc
      (dV bdA)ᴴ * dV bdA
       = (bdA.U * bdA.Uᴴ) * ((dV bdA)ᴴ * dV bdA) * (bdA.U * bdA.Uᴴ) := by
         rw [bdA.U_mul_star, m1m, mm1]
      _ = bdA.U * (bdA.Uᴴ * ((dV bdA)ᴴ * dV bdA) * bdA.U) * bdA.Uᴴ := by
         simp only [mma]
  _ = bdA.U * ((dV bdA * bdA.U)ᴴ * (dV bdA * bdA.U)) * bdA.Uᴴ := by
     simp only [ctM, mma]
  _ = 1 := by rw [h1, mm1, bdA.U_mul_star]
lemma dilRhoA'_mul_dilV {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) {c : Matrix (Fin d) (Fin d) ℂ} (hc : c ∈ comm A) :
  dilRhoA' bdA c * dV bdA = dV bdA * c := by
 have hcomm_c : bdA.Uᴴ * c * bdA.U = bDC bdA.r bdA.s (cBlk bdA c) :=
  commBlock_spec bdA hc
 have hVU_eq : dilRhoA' bdA c * (dV bdA * bdA.U) = (dV bdA * bdA.U) * (bdA.Uᴴ * c * bdA.U) := by
  rw [hcomm_c]
  ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, a₂, l₂⟩
  rw [mul_apply, mul_apply, Fintype.sum_sigma, Fintype.sum_sigma,
   sum_eq_single j₁, sum_eq_single j₁]
  ·
   simp only [sum_prod_type]
   have hL : ∑ x : Fin d, ∑ k : Fin (bdA.s j₁), ∑ l : Fin (bdA.s j₁),
     dilRhoA' bdA c ⟨j₁, x₁, k₁, l₁⟩ ⟨j₁, x, k, l⟩ * (dV bdA * bdA.U) ⟨j₁, x, k, l⟩ ⟨j₂, a₂, l₂⟩ =
     if h : j₁ = j₂ then
      cBlk bdA c j₁ l₁ (h ▸ l₂) *
       (((sqrt (bdA.s j₁ : ℝ) : ℂ)⁻¹) * bdA.U x₁ ⟨j₁, h ▸ a₂, k₁⟩)
     else 0 := by
    rw [sum_eq_single x₁]
    ·
     rw [sum_eq_single k₁]
     ·
      by_cases hj : j₁ = j₂
      ·
       subst hj
       simp only [↓reduceDIte]
       rw [sum_eq_single l₂]
       · simp [dilRhoA', dilV_mul_U]
       · intro l _ hl; simp [dilRhoA', dilV_mul_U, hl]
       · intro h; exact absurd (mem_univ l₂) h
      ·
       simp only [dif_neg hj]
       exact sum_eq_zero fun l _ => by simp [dilV_mul_U, hj]
     · intro k _ hk; exact sum_eq_zero fun l _ => by simp [dilRhoA', Ne.symm hk]
     · intro h; exact absurd (mem_univ k₁) h
    ·
     intro x _ hx; exact sum_eq_zero fun k _ => sum_eq_zero fun l _ => by
      simp [dilRhoA', Ne.symm hx]
    · intro h; exact absurd (mem_univ x₁) h
   have hR : ∑ a : Fin (bdA.r j₁), ∑ l : Fin (bdA.s j₁),
     (dV bdA * bdA.U) ⟨j₁, x₁, k₁, l₁⟩ ⟨j₁, a, l⟩ *
      bDC bdA.r bdA.s (cBlk bdA c) ⟨j₁, a, l⟩ ⟨j₂, a₂, l₂⟩ =
     if h : j₁ = j₂ then
      (((sqrt (bdA.s j₁ : ℝ) : ℂ)⁻¹) * bdA.U x₁ ⟨j₁, h ▸ a₂, k₁⟩) *
       cBlk bdA c j₁ l₁ (h ▸ l₂)
     else 0 := by
    by_cases hj : j₁ = j₂
    ·
     subst hj
     simp only [↓reduceDIte]
     rw [sum_eq_single a₂]
     ·
      rw [sum_eq_single l₁]
      · simp [dilV_mul_U, bDC]
      · intro l _ hl; simp [dilV_mul_U, Ne.symm hl]
      · intro h; exact absurd (mem_univ l₁) h
     · intro a _ ha; exact sum_eq_zero fun l _ => by simp [bDC, ha]
     · intro h; exact absurd (mem_univ a₂) h
    ·
     simp only [dif_neg hj]
     exact sum_eq_zero fun a _ => sum_eq_zero fun l _ => by simp [bDC, hj]
   rw [hL, hR]; by_cases hj : j₁ = j₂
   · subst hj; simp [mul_comm]
   · simp [hj]
  · intro j _ hjj; exact sum_eq_zero fun ⟨a, l⟩ _ => by simp [dilV_mul_U, Ne.symm hjj]
  · intro h; exact absurd (mem_univ j₁) h
  · intro j _ hjj; exact sum_eq_zero fun p _ => by simp [dilRhoA', Ne.symm hjj]
  · intro h; exact absurd (mem_univ j₁) h
 calc
  dilRhoA' bdA c * dV bdA = (dilRhoA' bdA c * (dV bdA * bdA.U)) * bdA.Uᴴ := by
     simp only [mma, bdA.U_mul_star, mm1]
  _ = ((dV bdA * bdA.U) * (bdA.Uᴴ * c * bdA.U)) * bdA.Uᴴ := by rw [hVU_eq]
  _ = dV bdA * ((bdA.U * bdA.Uᴴ) * c * (bdA.U * bdA.Uᴴ)) := by simp only [mma]
  _ = dV bdA * c := by rw [bdA.U_mul_star, m1m, mm1]
lemma dilV_star_dilRhoB_dilV {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (b : Matrix (Fin d) (Fin d) ℂ) :
  (dV bdA)ᴴ * dRB bdA b * dV bdA = cExp A b := by
 have hconj : (dV bdA * bdA.U)ᴴ * dRB bdA b * (dV bdA * bdA.U) =
   bDA bdA.r bdA.s (bCEM bdA b) := by
  ext ⟨j₁, a₁, l₁⟩ ⟨j₂, a₂, l₂⟩
  rw [mul_apply, Fintype.sum_sigma]
  have hmid : ∀ (j : Fin bdA.t) (x₂ : Fin d) (k₂ l' : Fin (bdA.s j)),
    ((dV bdA * bdA.U)ᴴ * dRB bdA b) ⟨j₁, a₁, l₁⟩ ⟨j, x₂, k₂, l'⟩ =
    if h : j₁ = j then if l₁ = h ▸ l' then
     ((sqrt (bdA.s j₁ : ℝ) : ℂ)⁻¹) * ∑ x₁ : Fin d, bdA.Uᴴ ⟨j₁, a₁, h ▸ k₂⟩ x₁ * b x₁ x₂
    else 0 else 0 := by
   intro j x₂ k₂ l'
   rw [mul_apply, Fintype.sum_sigma]
   by_cases hj : j₁ = j
   ·
    subst hj
    rw [sum_eq_single j₁]
    ·
     simp only [↓reduceDIte, sum_prod_type]
     by_cases hl : l₁ = l'
     ·
      subst hl
      simp only [↓reduceIte, Finset.mul_sum]
      refine sum_congr rfl fun x₁ _ => ?_
      rw [sum_eq_single k₂]
      ·
       rw [sum_eq_single l₁]
       ·
        rw [ctA, dilV_mul_U]
        simp only [dRB, of_apply, ↓reduceDIte, and_self, ↓reduceIte, star_mul,
         ctA]
        have hsr : star ((sqrt (bdA.s j₁ : ℝ) : ℂ)⁻¹) =
          ((sqrt (bdA.s j₁ : ℝ) : ℂ)⁻¹) := by
         rw [star_inv₀, star_def, conj_ofReal]
        rw [hsr]; ring
       · intro l _ hll; simp [dRB, hll]
       · intro h; exact absurd (mem_univ l₁) h
      · intro k _ hk; exact sum_eq_zero fun l _ => by simp [dRB, hk]
      · intro h; exact absurd (mem_univ k₂) h
     ·
      rw [if_neg hl]
      refine sum_eq_zero fun x₁ _ => sum_eq_zero fun k _ =>
       sum_eq_zero fun l _ => ?_
      by_cases hll : l = l'
      · subst hll; rw [ctA, dilV_mul_U]; simp [Ne.symm hl]
      · simp [dRB, hll]
    ·
     intro j' _ hjj
     refine sum_eq_zero fun p _ => ?_
     rw [ctA, dilV_mul_U, dif_neg hjj, star_zero, zero_mul]
    · intro h; exact absurd (mem_univ j₁) h
   ·
    rw [dif_neg hj]
    refine sum_eq_zero fun j' _ => sum_eq_zero fun p _ => ?_
    by_cases hjj : j' = j₁
    · subst hjj; simp [dRB, hj]
    · rw [ctA, dilV_mul_U, dif_neg hjj, star_zero, zero_mul]
  by_cases hj : j₁ = j₂
  ·
   subst hj
   rw [sum_eq_single j₁]
   ·
    simp only [sum_prod_type, bDA, ↓reduceDIte]
    by_cases hl : l₁ = l₂
    ·
     subst hl
     simp only [↓reduceIte]
     have hcol : ∀ (x₂ : Fin d) (k₂ : Fin (bdA.s j₁)),
       ∑ l' : Fin (bdA.s j₁), ((dV bdA * bdA.U)ᴴ * dRB bdA b) ⟨j₁, a₁, l₁⟩ ⟨j₁, x₂, k₂, l'⟩ *
        (dV bdA * bdA.U) ⟨j₁, x₂, k₂, l'⟩ ⟨j₁, a₂, l₁⟩ =
       (bdA.s j₁ : ℂ)⁻¹ * ((∑ x₁ : Fin d, bdA.Uᴴ ⟨j₁, a₁, k₂⟩ x₁ * b x₁ x₂) *
        bdA.U x₂ ⟨j₁, a₂, k₂⟩) := by
      intro x₂ k₂
      rw [sum_eq_single l₁]
      ·
       rw [hmid, dilV_mul_U]
       simp only [↓reduceDIte, ↓reduceIte]
       have hsq : ((sqrt (bdA.s j₁ : ℝ) : ℂ)⁻¹) * ((sqrt (bdA.s j₁ : ℝ) : ℂ)⁻¹) =
         (bdA.s j₁ : ℂ)⁻¹ := by
        rw [← mul_inv, ← ofReal_mul, mul_self_sqrt (Nat.cast_nonneg _),
         Complex.ofReal_natCast]
       linear_combination ((∑ x₁, bdA.Uᴴ ⟨j₁, a₁, k₂⟩ x₁ * b x₁ x₂) * bdA.U x₂ ⟨j₁, a₂, k₂⟩) * hsq
      · intro l' _ hll; rw [dilV_mul_U]; simp [hll]
      · intro h; exact absurd (mem_univ l₁) h
     simp_rw [hcol]
     rw [sum_comm]
     simp_rw [← Finset.mul_sum]
     dsimp only [bCEM]
     congr 1
    ·
     rw [if_neg hl]
     refine sum_eq_zero fun x₂ _ => sum_eq_zero fun k₂ _ =>
      sum_eq_zero fun l' _ => ?_
     rw [hmid, dilV_mul_U]
     by_cases hll : l₁ = l'
     · subst hll; simp [hl]
     · simp [hll]
   ·
    intro j _ hjj
    refine sum_eq_zero fun p _ => ?_
    rw [hmid, dif_neg (Ne.symm hjj), zero_mul]
   · intro h; exact absurd (mem_univ j₁) h
  ·
   simp only [bDA, dif_neg hj]
   refine sum_eq_zero fun j _ => sum_eq_zero fun p _ => ?_
   rw [hmid, dilV_mul_U]
   by_cases h1 : j₁ = j
   · subst h1; simp [hj]
   · simp [h1]
 rw [condExp_eq_blockDiagA bdA b, ← hconj]
 calc
  (dV bdA)ᴴ * dRB bdA b * dV bdA
   = (bdA.U * bdA.Uᴴ) * ((dV bdA)ᴴ * dRB bdA b * dV bdA) * (bdA.U * bdA.Uᴴ) := by
     rw [bdA.U_mul_star, m1m, mm1]
  _ = bdA.U * ((dV bdA * bdA.U)ᴴ * dRB bdA b * (dV bdA * bdA.U)) * bdA.Uᴴ := by
     simp only [ctM, mma]
lemma hsSq_dilRhoB_mul_dilV_sub {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) (b : Matrix (Fin d) (Fin d) ℂ) :
  hsSq (dRB bdA b * dV bdA - dV bdA * b) = 2 * hsSq (b - cExp A b) := by
 rw [hsSq_tr, ctS, msm, mms, mms,
  trace_sub, trace_sub, trace_sub, sub_re, sub_re,
  sub_re]
 have h1 : ((dRB bdA b * dV bdA)ᴴ * (dRB bdA b * dV bdA)).trace = (bᴴ * b).trace := by
  calc
   ((dRB bdA b * dV bdA)ᴴ * (dRB bdA b * dV bdA)).trace
    = ((dV bdA)ᴴ * dRB bdA (bᴴ * b) * dV bdA).trace := by
      rw [ctM, dilRhoB_mul, dilRhoB_star]; simp only [mma]
   _ = (cExp A (bᴴ * b)).trace := by rw [dilV_star_dilRhoB_dilV]
   _ = ((1 : Matrix (Fin d) (Fin d) ℂ)ᴴ * cExp A (bᴴ * b)).trace := by simp
   _ = ((1 : Matrix (Fin d) (Fin d) ℂ)ᴴ * (bᴴ * b)).trace := by
      have h := congrArg star (condExp_inner_eq A (bᴴ * b) A.one_mem)
      rw [← trace_conjTranspose, ← trace_conjTranspose, ctM,
       ctM, ctct,
       ctct] at h
      exact h
   _ = (bᴴ * b).trace := by simp
 have h2 : ((dRB bdA b * dV bdA)ᴴ * (dV bdA * b)).trace =
   ((cExp A b)ᴴ * cExp A b).trace := by
  have hce : ((dV bdA)ᴴ * dRB bdA b * dV bdA)ᴴ =
    (dV bdA)ᴴ * dRB bdA bᴴ * dV bdA := by
   simp only [ctM, ctct, dilRhoB_star, mma]
  calc
   ((dRB bdA b * dV bdA)ᴴ * (dV bdA * b)).trace
    = (((dV bdA)ᴴ * dRB bdA bᴴ * dV bdA) * b).trace := by
      rw [ctM, dilRhoB_star]; simp only [mma]
   _ = ((cExp A b)ᴴ * b).trace := by rw [← hce, dilV_star_dilRhoB_dilV]
   _ = ((cExp A b)ᴴ * cExp A b).trace := by
      have h := congrArg star (condExp_inner_eq A b (condExp_mem A b))
      rw [← trace_conjTranspose, ← trace_conjTranspose, ctM,
       ctM, ctct,
       ctct] at h
      exact h.symm
 have h3 : ((dV bdA * b)ᴴ * (dRB bdA b * dV bdA)).trace =
   ((cExp A b)ᴴ * cExp A b).trace := by
  have h := congrArg star h2
  rw [← trace_conjTranspose, ← trace_conjTranspose] at h
  simpa [ctM] using h
 have h4 : ((dV bdA * b)ᴴ * (dV bdA * b)).trace = (bᴴ * b).trace := by
  rw [ctM, mma, ← mma (dV bdA)ᴴ, dilV_star_mul,
   m1m]
 rw [h1, h2, h3, h4, ← hsSq_tr b, ← hsSq_tr (cExp A b)]
 linarith [hsSq_eq_hsSq_condExp_add A b]
lemma dilRhoB_mul_dilV_of_mem {d : ℕ} {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) {x : Matrix (Fin d) (Fin d) ℂ} (hx : x ∈ A) :
  dRB bdA x * dV bdA = dV bdA * x := by
 apply sub_eq_zero.mp
 apply (hsSq_eq_zero_iff _).mp
 rw [hsSq_dilRhoB_mul_dilV_sub, condExp_eq_self hx, sub_self,
  show hsSq (0 : Matrix (Fin d) (Fin d) ℂ) = 0 by simp [hsSq], mul_zero]
lemma exists_dilation_cutoff {d : ℕ}
  {B A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdB : BDec B) (bdA : BDec A) {ε : ℝ}
  (hinc : ∀ b ∈ B, ‖CLM b‖ ≤ 1 → hsSq (b - cExp A b) ≤ ε ^ 2 * (d : ℝ)) :
  ∃ Q : Matrix (DilK bdA) (DilK bdA) ℂ,
   Q.IsHermitian ∧ Q * Q = Q ∧
   (∀ b ∈ B, dRB bdA b * Q = Q * dRB bdA b) ∧
   (∀ c ∈ comm A, dilRhoA' bdA c * Q = Q * dilRhoA' bdA c) ∧
   |(Q.trace).re - (d : ℝ)| ≤ 2 * ε ^ 2 * (d : ℝ) ∧
   hsSq ((1 - Q) * dV bdA) ≤ 2 * ε ^ 2 * (d : ℝ) := by
 classical
 let K := DilK bdA
 let V := dV bdA
 let N : ℝ := (Fintype.card (BHW bdB) : ℝ)
 have hNpos : 0 < N := Nat.cast_pos.mpr (blockHW_card_pos bdB)
 have hN0 : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hNpos)
 let Pg (g : BHW bdB) : Matrix K K ℂ :=
  dRB bdA (bHW bdB g) * (V * Vᴴ) * (dRB bdA (bHW bdB g))ᴴ
 have hPg_herm : ∀ g, (Pg g).IsHermitian := fun g => by
  dsimp only [Pg, IsHermitian]
  simp only [ctM, ctct, mma]
 have hPg_proj : ∀ g, Pg g * Pg g = Pg g := fun g => by
  have hU := bHW_u bdB g
  have hUs : (dRB bdA (bHW bdB g))ᴴ * dRB bdA (bHW bdB g) = 1 := by
   rw [← dilRhoB_star, ← dilRhoB_mul, ← star_eq_conjTranspose,
    star_mul_self_of_mem hU, dilRhoB_one]
  dsimp only [Pg]
  calc
   dRB bdA (bHW bdB g) * (V * Vᴴ) * (dRB bdA (bHW bdB g))ᴴ *
     (dRB bdA (bHW bdB g) * (V * Vᴴ) * (dRB bdA (bHW bdB g))ᴴ)
    = dRB bdA (bHW bdB g) * (V * Vᴴ) *
      (((dRB bdA (bHW bdB g))ᴴ * dRB bdA (bHW bdB g)) * (V * Vᴴ)) *
      (dRB bdA (bHW bdB g))ᴴ := by simp only [mma]
   _ = dRB bdA (bHW bdB g) * (V * ((Vᴴ * V) * Vᴴ)) * (dRB bdA (bHW bdB g))ᴴ := by
      rw [hUs, m1m]; simp only [mma]
   _ = dRB bdA (bHW bdB g) * (V * Vᴴ) * (dRB bdA (bHW bdB g))ᴴ := by
      rw [dilV_star_mul, m1m]
 let h : Matrix K K ℂ := ((N : ℂ)⁻¹) • ∑ g : BHW bdB, Pg g
 have hh_herm : h.IsHermitian := by
  dsimp only [h, IsHermitian]
  rw [conjTranspose_smul, conjTranspose_sum]
  have hinv : star ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ := by
   rw [star_inv₀, star_def, conj_ofReal]
  rw [hinv]
  congr 1
  exact sum_congr rfl fun g _ => (hPg_herm g).eq
 have hh_comm_B : ∀ b ∈ B, dRB bdA b * h = h * dRB bdA b := by
  let slice (X : Matrix (DilK bdA) (DilK bdA) ℂ) (α β : Σ j : Fin bdA.t, Fin (bdA.s j) × Fin (bdA.s j)) :
    Matrix (Fin d) (Fin d) ℂ :=
   Matrix.of fun x₁ x₂ => X ⟨α.1, x₁, α.2.1, α.2.2⟩ ⟨β.1, x₂, β.2.1, β.2.2⟩
  have hslice_left : ∀ (b : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (DilK bdA) (DilK bdA) ℂ) α β,
    slice (dRB bdA b * X) α β = b * slice X α β := by
   intro b X α β; ext x₁ x₂
   simp only [slice, of_apply, mul_apply, Fintype.sum_sigma]
   rw [sum_eq_single α.1]
   ·
    simp only [dRB, of_apply, ↓reduceDIte, sum_prod_type]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_eq_single α.2.1]
    ·
     rw [sum_eq_single α.2.2]
     · simp
     · intro l _ hl; simp [Ne.symm hl]
     · intro h; exact absurd (mem_univ α.2.2) h
    · intro k _ hk; exact sum_eq_zero fun l _ => by simp [Ne.symm hk]
    · intro h; exact absurd (mem_univ α.2.1) h
   · intro j _ hj; exact sum_eq_zero fun p _ => by simp [dRB, Ne.symm hj]
   · intro h; exact absurd (mem_univ α.1) h
  have hslice_right : ∀ (X : Matrix (DilK bdA) (DilK bdA) ℂ) (b : Matrix (Fin d) (Fin d) ℂ) α β,
    slice (X * dRB bdA b) α β = slice X α β * b := by
   intro X b α β; ext x₁ x₂
   simp only [slice, of_apply, mul_apply, Fintype.sum_sigma]
   rw [sum_eq_single β.1]
   ·
    simp only [dRB, of_apply, ↓reduceDIte, sum_prod_type]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_eq_single β.2.1]
    ·
     rw [sum_eq_single β.2.2]
     · simp
     · intro l _ hl; simp [hl]
     · intro h; exact absurd (mem_univ β.2.2) h
    · intro k _ hk; exact sum_eq_zero fun l _ => by simp [hk]
    · intro h; exact absurd (mem_univ β.2.1) h
   · intro j _ hj; exact sum_eq_zero fun p _ => by simp [dRB, hj]
   · intro h; exact absurd (mem_univ β.1) h
  have hslice_h : ∀ α β, slice h α β ∈ comm B := by
   intro α β
   have heq : slice h α β = cExp (comm B) (slice (V * Vᴴ) α β) := by
    rw [condExp_commutant_eq_avg bdB]
    ext x₁ x₂
    simp only [slice, of_apply, h, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
     N, Complex.ofReal_natCast]
    congr 1
    refine sum_congr rfl fun g _ => ?_
    have hstep : slice (Pg g) α β =
      bHW bdB g * slice (V * Vᴴ) α β * (bHW bdB g)ᴴ := by
     dsimp only [Pg]
     rw [← dilRhoB_star, hslice_right, hslice_left]
    exact congrFun (congrFun hstep x₁) x₂
   rw [heq]; exact condExp_mem (comm B) _
  intro b hb
  ext ⟨j₁, x₁, k₁, l₁⟩ ⟨j₂, x₂, k₂, l₂⟩
  have h1 := congrFun (congrFun (hslice_left b h ⟨j₁, k₁, l₁⟩ ⟨j₂, k₂, l₂⟩) x₁) x₂
  have h2 := congrFun (congrFun (hslice_right h b ⟨j₁, k₁, l₁⟩ ⟨j₂, k₂, l₂⟩) x₁) x₂
  have h3 := congrFun (congrFun ((hslice_h ⟨j₁, k₁, l₁⟩ ⟨j₂, k₂, l₂⟩) b hb) x₁) x₂
  exact h1.trans (h3.symm.trans h2.symm)
 have hh_comm_A' : ∀ c ∈ comm A, dilRhoA' bdA c * h = h * dilRhoA' bdA c := by
  intro c hc
  dsimp only [h]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  refine sum_congr rfl fun g _ => ?_
  have hVV : dilRhoA' bdA c * (V * Vᴴ) = (V * Vᴴ) * dilRhoA' bdA c := by
   have hc' : cᴴ ∈ comm A := star_mem hc
   have hVh : Vᴴ * dilRhoA' bdA c = c * Vᴴ := by
    have h1 := congrArg Matrix.conjTranspose (dilRhoA'_mul_dilV bdA hc')
    rw [ctM, ctM, ← dilRhoA'_star,
     ctct] at h1
    exact h1
   calc
    dilRhoA' bdA c * (V * Vᴴ) = (dilRhoA' bdA c * V) * Vᴴ := by simp only [mma]
    _ = V * (c * Vᴴ) := by
       dsimp only [V]; rw [dilRhoA'_mul_dilV bdA hc]; simp only [mma]
    _ = (V * Vᴴ) * dilRhoA' bdA c := by rw [← hVh]; simp only [mma]
  dsimp only [Pg]
  calc
   dilRhoA' bdA c * (dRB bdA (bHW bdB g) * (V * Vᴴ) * (dRB bdA (bHW bdB g))ᴴ)
    = (dilRhoA' bdA c * dRB bdA (bHW bdB g)) * (V * Vᴴ) * (dRB bdA (bHW bdB g))ᴴ := by
      simp only [mma]
   _ = dRB bdA (bHW bdB g) * (dilRhoA' bdA c * (V * Vᴴ)) * (dRB bdA (bHW bdB g))ᴴ := by
      rw [← dilRho_comm]; simp only [mma]
   _ = dRB bdA (bHW bdB g) * (V * Vᴴ) * (dilRhoA' bdA c * (dRB bdA (bHW bdB g))ᴴ) := by
      rw [hVV]; simp only [mma]
   _ = dRB bdA (bHW bdB g) * (V * Vᴴ) * (dRB bdA (bHW bdB g))ᴴ * dilRhoA' bdA c := by
      rw [← dilRhoB_star, ← dilRho_comm]; simp only [mma]
 have hh_eig_bounds : ∀ α : K, 0 ≤ hh_herm.eigenvalues α ∧ hh_herm.eigenvalues α ≤ 1 := by
  intro α
  let v := hh_herm.eigenvectorBasis α
  have hv_norm : ‖v‖ = 1 := hh_herm.eigenvectorBasis.orthonormal.1 α
  have hv_eig : CLM h v = (hh_herm.eigenvalues α : ℂ) • v := by
   apply WithLp.ofLp_injective
   simpa [ofLp_toEuclideanCLM, RCLike.real_smul_eq_coe_smul] using
    hh_herm.mulVec_eigenvectorBasis α
  have havg : hh_herm.eigenvalues α = N⁻¹ * ∑ g : BHW bdB, ‖CLM (Pg g) v‖ ^ 2 := by
   have hC : (hh_herm.eigenvalues α : ℂ) =
     ((N : ℂ)⁻¹) * ∑ g : BHW bdB, ((‖CLM (Pg g) v‖ ^ 2 : ℝ) : ℂ) := by
    have hinner : (hh_herm.eigenvalues α : ℂ) = ⟪v, CLM h v⟫_ℂ := by
     rw [hv_eig, inner_smul_right, inner_self_eq_norm_sq_to_K, hv_norm]; simp
    rw [hinner]
    dsimp only [h, CLM]
    rw [map_smul, map_sum, FunLike.coe_smul, Pi.smul_apply, FunLike.coe_sum, Finset.sum_apply,
     inner_smul_right, inner_sum]
    congr 1
    refine sum_congr rfl fun g _ => proj_inner_eq_norm_sq (hPg_herm g) (hPg_proj g) v
   rw [← Complex.ofReal_sum, ← Complex.ofReal_inv, ← ofReal_mul] at hC
   exact Complex.ofReal_injective hC
  constructor
  ·
   rw [havg]
   exact mul_nonneg (inv_nonneg.mpr (le_of_lt hNpos)) (sum_nonneg fun g _ => sq_nonneg _)
  ·
   rw [havg]
   calc
    N⁻¹ * ∑ g : BHW bdB, ‖CLM (Pg g) v‖ ^ 2
     ≤ N⁻¹ * ∑ _g : BHW bdB, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left
       (sum_le_sum fun g _ => by
        have := proj_norm_sq_le (hPg_herm g) (hPg_proj g) v; rwa [hv_norm, one_pow] at this)
       (inv_nonneg.mpr (le_of_lt hNpos))
    _ = 1 := by
      rw [sum_const, card_univ, nsmul_eq_mul, mul_one,
       inv_mul_cancel₀ (ne_of_gt hNpos)]
 have hh_tr : h.trace = (d : ℂ) := by
  dsimp only [h]
  rw [trace_smul, trace_sum, smul_eq_mul]
  have htr_g : ∀ g : BHW bdB, (Pg g).trace = (d : ℂ) := by
   intro g
   have hU := bHW_u bdB g
   have hUs : (dRB bdA (bHW bdB g))ᴴ * dRB bdA (bHW bdB g) = 1 := by
    rw [← dilRhoB_star, ← dilRhoB_mul, ← star_eq_conjTranspose,
     star_mul_self_of_mem hU, dilRhoB_one]
   dsimp only [Pg]
   calc
    (dRB bdA (bHW bdB g) * (V * Vᴴ) * (dRB bdA (bHW bdB g))ᴴ).trace
     = ((dRB bdA (bHW bdB g))ᴴ * (dRB bdA (bHW bdB g) * (V * Vᴴ))).trace :=
       trace_mul_comm _ _
    _ = (((dRB bdA (bHW bdB g))ᴴ * dRB bdA (bHW bdB g)) * (V * Vᴴ)).trace := by
       simp only [mma]
    _ = (V * Vᴴ).trace := by rw [hUs, m1m]
    _ = (Vᴴ * V).trace := trace_mul_comm _ _
    _ = (d : ℂ) := by rw [dilV_star_mul, trace_one, card_fin]
  simp_rw [htr_g, sum_const, card_univ, nsmul_eq_mul, ← mul_assoc]
  change (N : ℂ)⁻¹ * (N : ℂ) * (d : ℂ) = (d : ℂ)
  rw [inv_mul_cancel₀ hN0, one_mul]
 have hh_sq_tr : (h * h).trace = (Vᴴ * h * V).trace := by
  have h_eq : h * h = h * ((N : ℂ)⁻¹ • ∑ g : BHW bdB, Pg g) := rfl
  rw [h_eq, Matrix.mul_smul, Matrix.mul_sum, trace_smul, trace_sum, smul_eq_mul]
  have hterm : ∀ g : BHW bdB, (h * Pg g).trace = (Vᴴ * h * V).trace := by
   intro g
   have hU := bHW_u bdB g
   have hUs : (dRB bdA (bHW bdB g))ᴴ * dRB bdA (bHW bdB g) = 1 := by
    rw [← dilRhoB_star, ← dilRhoB_mul, ← star_eq_conjTranspose,
     star_mul_self_of_mem hU, dilRhoB_one]
   have hcomm := hh_comm_B _ (blockHWMat_mem bdB g)
   dsimp only [Pg]
   calc
    (h * (dRB bdA (bHW bdB g) * (V * Vᴴ) * (dRB bdA (bHW bdB g))ᴴ)).trace
     = ((h * dRB bdA (bHW bdB g) * (V * Vᴴ)) * (dRB bdA (bHW bdB g))ᴴ).trace := by
       simp only [mma]
    _ = ((dRB bdA (bHW bdB g))ᴴ * (h * dRB bdA (bHW bdB g) * (V * Vᴴ))).trace :=
       trace_mul_comm _ _
    _ = ((dRB bdA (bHW bdB g))ᴴ * (dRB bdA (bHW bdB g) * h * (V * Vᴴ))).trace := by
       rw [← hcomm]
    _ = (((dRB bdA (bHW bdB g))ᴴ * dRB bdA (bHW bdB g)) * (h * (V * Vᴴ))).trace := by
       simp only [mma]
    _ = ((h * V) * Vᴴ).trace := by rw [hUs, m1m, mma]
    _ = (Vᴴ * h * V).trace := by rw [trace_mul_comm, mma]
  simp_rw [hterm]
  rw [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc]
  change (N : ℂ)⁻¹ * (N : ℂ) * (Vᴴ * h * V).trace = (Vᴴ * h * V).trace
  rw [inv_mul_cancel₀ hN0, one_mul]
 have hVhV_re : ((Vᴴ * (1 - h) * V).trace).re ≤ ε ^ 2 * (d : ℝ) := by
  have hVhV : ((Vᴴ * h * V).trace).re =
    N⁻¹ * ∑ g : BHW bdB, hsSq (cExp A (bHW bdB g)) := by
   dsimp only [h]
   rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
    trace_smul, trace_sum, smul_eq_mul]
   have hterm : ∀ g : BHW bdB,
     (Vᴴ * Pg g * V).trace = ((hsSq (cExp A (bHW bdB g)) : ℝ) : ℂ) := by
    intro g
    dsimp only [Pg]
    have h1 : Vᴴ * (dRB bdA (bHW bdB g) * (V * Vᴴ) * (dRB bdA (bHW bdB g))ᴴ) * V =
      (Vᴴ * dRB bdA (bHW bdB g) * V) * (Vᴴ * dRB bdA (bHW bdB g) * V)ᴴ := by
     simp only [ctM, ctct, mma]
    rw [h1, dilV_star_dilRhoB_dilV, trace_mul_comm, hsSq_trC]
   simp_rw [hterm]
   rw [← Complex.ofReal_sum, ← Complex.ofReal_inv, ← ofReal_mul, Complex.ofReal_re]
  have hsub : ((Vᴴ * (1 - h) * V).trace).re = (d : ℝ) - ((Vᴴ * h * V).trace).re := by
   rw [mms, mm1, msm, trace_sub, sub_re,
    dilV_star_mul, trace_one, card_fin]; simp
  rw [hsub, hVhV]
  have havg_bound : N⁻¹ * ∑ g : BHW bdB, hsSq (bHW bdB g - cExp A (bHW bdB g)) ≤
    ε ^ 2 * (d : ℝ) := by
   calc
    N⁻¹ * ∑ g : BHW bdB, hsSq (bHW bdB g - cExp A (bHW bdB g))
     ≤ N⁻¹ * ∑ _g : BHW bdB, (ε ^ 2 * (d : ℝ)) :=
      mul_le_mul_of_nonneg_left
       (sum_le_sum fun g _ =>
        hinc _ (blockHWMat_mem bdB g) (opNorm_unitary_le' (bHW_u bdB g)))
       (inv_nonneg.mpr (le_of_lt hNpos))
    _ = ε ^ 2 * (d : ℝ) := by
      rw [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc,
       inv_mul_cancel₀ (ne_of_gt hNpos), one_mul]
  have hdiff_eq : (d : ℝ) - N⁻¹ * ∑ g : BHW bdB, hsSq (cExp A (bHW bdB g)) =
    N⁻¹ * ∑ g : BHW bdB, hsSq (bHW bdB g - cExp A (bHW bdB g)) := by
   have hterm : ∀ g : BHW bdB,
     hsSq (bHW bdB g - cExp A (bHW bdB g)) =
      (d : ℝ) - hsSq (cExp A (bHW bdB g)) := by
    intro g
    have h1 := hsSq_eq_hsSq_condExp_add A (bHW bdB g)
    have h2 : hsSq (bHW bdB g) = (d : ℝ) := by
     rw [hsSq_tr, ← star_eq_conjTranspose,
      star_mul_self_of_mem (bHW_u bdB g),
      trace_one, card_fin]; simp
    linarith
   simp_rw [hterm]
   rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
    mul_sub, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hNpos), one_mul]
  linarith
 have hh_1h_re : ((h * (1 - h)).trace).re ≤ ε ^ 2 * (d : ℝ) := by
  have heq : ((h * (1 - h)).trace).re = ((Vᴴ * (1 - h) * V).trace).re := by
   rw [mms, mm1, trace_sub, hh_tr, hh_sq_tr,
    mms, mm1, msm, trace_sub, dilV_star_mul,
    trace_one, card_fin]
  rw [heq]; exact hVhV_re
 let Q : Matrix K K ℂ := hh_herm.cfc (fun t => if (1 / 2 : ℝ) ≤ t then 1 else 0)
 have hQh : Q.IsHermitian := cfc_isHermitian hh_herm _
 have hQp : Q * Q = Q := by
  dsimp only [Q]; rw [cfc_mul]
  refine cfc_congr hh_herm fun α => by by_cases h12 : (1 / 2 : ℝ) ≤ hh_herm.eigenvalues α <;> simp
 have hQ_tr_diff : |(Q.trace).re - (d : ℝ)| ≤ 2 * ε ^ 2 * (d : ℝ) := by
  have htrQ : (Q.trace).re = ∑ α : K, if (1 / 2 : ℝ) ≤ hh_herm.eigenvalues α then (1 : ℝ) else 0 := by
   dsimp only [Q]; rw [trace_cfc, re_sum]; simp
  have htrh : (d : ℝ) = ∑ α : K, hh_herm.eigenvalues α := by
   have h1 : h.trace = ∑ α : K, (hh_herm.eigenvalues α : ℂ) := by
    conv_lhs => rw [← cfc_id hh_herm]
    rw [trace_cfc]; rfl
   have hre := congrArg Complex.re (hh_tr.symm.trans h1)
   simpa [re_sum] using hre
  have h1h : ∑ α : K, hh_herm.eigenvalues α * (1 - hh_herm.eigenvalues α) =
    ((h * (1 - h)).trace).re := by
   have h1 : h * (1 - h) = hh_herm.cfc (fun t => t * (1 - t)) := by
    have h1' : (1 : Matrix K K ℂ) - h = hh_herm.cfc (fun t => 1 - t) := by
     rw [← cfc_sub hh_herm (fun _ => 1) (fun t => t), cfc_one hh_herm,
      show hh_herm.cfc (fun t => t) = h from cfc_id hh_herm]
    conv_lhs => arg 1; rw [← cfc_id hh_herm]
    rw [h1', cfc_mul]; rfl
   rw [h1, trace_cfc, re_sum]; simp
  conv_lhs => rw [htrQ, htrh, ← sum_sub_distrib]
  calc
   |∑ α : K, ((if (1 / 2 : ℝ) ≤ hh_herm.eigenvalues α then (1 : ℝ) else 0) - hh_herm.eigenvalues α)|
    ≤ ∑ α : K, |(if (1 / 2 : ℝ) ≤ hh_herm.eigenvalues α then (1 : ℝ) else 0) - hh_herm.eigenvalues α| :=
     abs_sum_le_sum_abs _ _
   _ ≤ ∑ α : K, 2 * (hh_herm.eigenvalues α * (1 - hh_herm.eigenvalues α)) := by
     refine sum_le_sum fun α _ => ?_
     rcases hh_eig_bounds α with ⟨h0, h1⟩
     by_cases h12 : (1 / 2 : ℝ) ≤ hh_herm.eigenvalues α
     · rw [if_pos h12, abs_of_nonneg (by linarith)]; nlinarith
     · rw [if_neg h12, zero_sub, abs_neg, abs_of_nonneg h0]; nlinarith
   _ = 2 * ((h * (1 - h)).trace).re := by rw [← Finset.mul_sum, h1h]
   _ ≤ 2 * (ε ^ 2 * (d : ℝ)) := by linarith
   _ = 2 * ε ^ 2 * (d : ℝ) := by ring
 have hhs_1Q_V : hsSq ((1 - Q) * V) ≤ 2 * ε ^ 2 * (d : ℝ) := by
  have h1Q_eq : hsSq ((1 - Q) * V) = ((Vᴴ * (1 - Q) * V).trace).re := by
   rw [hsSq_tr, ctM, ctS,
    conjTranspose_one, hQh.eq]
   have h1Qp : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [msm, mms, mms, m1m, m1m,
     mm1, hQp]; abel
   calc
    (Vᴴ * (1 - Q) * ((1 - Q) * V)).trace.re
     = (Vᴴ * ((1 - Q) * (1 - Q)) * V).trace.re := by simp only [mma]
    _ = (Vᴴ * (1 - Q) * V).trace.re := by rw [h1Qp]
  let g : ℝ → ℝ := fun t => 2 * (1 - t) - (if (1 / 2 : ℝ) ≤ t then 0 else 1)
  let R : Matrix K K ℂ := hh_herm.cfc (fun t => sqrt (g t))
  have hR_sq : Rᴴ * R = (2 : ℂ) • (1 - h) - (1 - Q) := by
   have hRh : Rᴴ = R := (cfc_isHermitian hh_herm _).eq
   rw [hRh]; dsimp only [R, Q]; rw [cfc_mul]
   have hRhs : (2 : ℂ) • (1 - h) - (1 - hh_herm.cfc (fun t => if (1 / 2 : ℝ) ≤ t then 1 else 0)) =
     hh_herm.cfc g := by
    have h1 : (1 : Matrix K K ℂ) - h = hh_herm.cfc (fun t => 1 - t) := by
     rw [← cfc_sub hh_herm (fun _ => 1) (fun t => t), cfc_one hh_herm,
      show hh_herm.cfc (fun t => t) = h from cfc_id hh_herm]
    have h2 : (2 : ℂ) • (1 - h) = hh_herm.cfc (fun t => 2 * (1 - t)) := by
     have hc : (2 : ℂ) • (1 : Matrix K K ℂ) = hh_herm.cfc (fun _ => 2) := (cfc_const hh_herm 2).symm
     calc
      (2 : ℂ) • (1 - h) = ((2 : ℂ) • (1 : Matrix K K ℂ)) * (1 - h) := by
         rw [Matrix.smul_mul, m1m]
      _ = hh_herm.cfc (fun _ => 2) * hh_herm.cfc (fun t => 1 - t) := by rw [hc, h1]
      _ = hh_herm.cfc (fun t => 2 * (1 - t)) := cfc_mul hh_herm _ _
    have h3 : (1 : Matrix K K ℂ) - hh_herm.cfc (fun t => if (1 / 2 : ℝ) ≤ t then 1 else 0) =
      hh_herm.cfc (fun t => if (1 / 2 : ℝ) ≤ t then 0 else 1) := by
     rw [← cfc_one hh_herm, cfc_sub]
     refine cfc_congr hh_herm fun α => by split_ifs <;> norm_num
    rw [h2, h3, cfc_sub]
   rw [hRhs]
   refine cfc_congr hh_herm fun α => ?_
   rcases hh_eig_bounds α with ⟨h0, h1⟩
   have hg_nn : 0 ≤ g (hh_herm.eigenvalues α) := by
    dsimp only [g]; by_cases h12 : (1 / 2 : ℝ) ≤ hh_herm.eigenvalues α
    · rw [if_pos h12]; linarith
    · rw [if_neg h12]; linarith
   exact mul_self_sqrt hg_nn
  have hdiff_nn : 0 ≤ 2 * ((Vᴴ * (1 - h) * V).trace).re - ((Vᴴ * (1 - Q) * V).trace).re := by
   have h1 : hsSq (R * V) = 2 * ((Vᴴ * (1 - h) * V).trace).re - ((Vᴴ * (1 - Q) * V).trace).re := by
    rw [hsSq_tr]
    have hprod : (R * V)ᴴ * (R * V) = (2 : ℂ) • (Vᴴ * (1 - h) * V) - Vᴴ * (1 - Q) * V := by
     calc
      (R * V)ᴴ * (R * V) = Vᴴ * (Rᴴ * R) * V := by
         simp only [ctM, mma]
      _ = Vᴴ * ((2 : ℂ) • (1 - h) - (1 - Q)) * V := by rw [hR_sq]
      _ = (2 : ℂ) • (Vᴴ * (1 - h) * V) - Vᴴ * (1 - Q) * V := by
         rw [mms, msm, Matrix.mul_smul, Matrix.smul_mul]
    rw [hprod, trace_sub, trace_smul, sub_re, smul_eq_mul]
    simp
   rw [← h1]; exact hsSq_nonneg _
  rw [h1Q_eq]; linarith
 exact ⟨Q, hQh, hQp,
  fun b hb => cfc_commute hh_herm (dRB bdA b) (hh_comm_B b hb) _,
  fun c hc => cfc_commute hh_herm (dilRhoA' bdA c) (hh_comm_A' c hc) _,
  hQ_tr_diff, hhs_1Q_V⟩
lemma exists_bratteli_polar {d m : ℕ}
  {B A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} (bdA : BDec A)
  {ε : ℝ} (hε : 0 ≤ ε)
  (hinc : ∀ b ∈ B, ‖CLM b‖ ≤ 1 → hsSq (b - cExp A b) ≤ ε ^ 2 * (d : ℝ))
  {Q : Matrix (DilK bdA) (DilK bdA) ℂ} (hQh : Q.IsHermitian) (hQp : Q * Q = Q)
  (hQ_comm_B : ∀ b ∈ B, dRB bdA b * Q = Q * dRB bdA b)
  (hQ_comm_A' : ∀ c ∈ comm A, dilRhoA' bdA c * Q = Q * dilRhoA' bdA c)
  (hhs_1Q_V : hsSq ((1 - Q) * dV bdA) ≤ 2 * ε ^ 2 * (d : ℝ))
  {ιQ : Matrix (DilK bdA) (Fin m) ℂ} (hιQ_star : ιQᴴ * ιQ = 1) (hιQ_mul : ιQ * ιQᴴ = Q)
  (hm_diff : |(m : ℝ) - (d : ℝ)| ≤ 2 * ε ^ 2 * (d : ℝ)) :
  let πB := fun b => ιQᴴ * dRB bdA b * ιQ
  let πA' := fun c => ιQᴴ * dilRhoA' bdA c * ιQ
  ∃ W : Matrix (Fin m) (Fin d) ℂ,
   (Wᴴ * W) * (Wᴴ * W) = Wᴴ * W ∧
   (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ ∧
   ((1 - Wᴴ * W).trace).re ≤ 2 * ε ^ 2 * (d : ℝ) ∧
   ((1 - W * Wᴴ).trace).re ≤ 4 * ε ^ 2 * (d : ℝ) ∧
   (∀ c ∈ comm A, πA' c * W = W * c) ∧
   (∀ x ∈ A, x ∈ B → πB x * W = W * x) ∧
   (∀ b ∈ B, ‖CLM b‖ ≤ 1 → hsN (πB b * W - W * b) ≤ 6 * ε * sqrt (d : ℝ)) := by
 intro πB πA'
 let K := DilK bdA
 let V := dV bdA
 let S : Matrix (Fin d) (Fin d) ℂ := Vᴴ * Q * V
 have hS : S.IsHermitian := by
  dsimp only [S, IsHermitian]
  simp only [ctM, ctct, hQh.eq, mma]
 have hS_eig : ∀ i : Fin d, 0 ≤ hS.eigenvalues i ∧ hS.eigenvalues i ≤ 1 := by
  intro i
  let v := hS.eigenvectorBasis i
  have hv_norm : ‖v‖ = 1 := hS.eigenvectorBasis.orthonormal.1 i
  let hVv : EuclideanSpace ℂ K := WithLp.toLp 2 (V.mulVec v.ofLp)
  have hVv_norm : ‖hVv‖ ^ 2 = 1 := by
   have hC : ((‖hVv‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [show ((‖hVv‖ ^ 2 : ℝ) : ℂ) = ⟪hVv, hVv⟫_ℂ by rw [inner_self_eq_norm_sq_to_K]; simp]
    change ∑ p : K, (V.mulVec v.ofLp p) * star (V.mulVec v.ofLp p) = 1
    have h1 : ∑ p : K, (V.mulVec v.ofLp p) * star (V.mulVec v.ofLp p) =
      ∑ x : Fin d, (Vᴴ * V).mulVec v.ofLp x * star (v.ofLp x) := by
     simp only [mulVec, dotProduct, mul_apply, Finset.sum_mul, Finset.mul_sum,
      star_sum, star_mul, ctA]
     rw [sum_comm]
     refine sum_congr rfl fun x _ => ?_
     rw [sum_comm]
     refine sum_congr rfl fun y _ => sum_congr rfl fun p _ => by ring
    rw [h1, dilV_star_mul, Matrix.one_mulVec]
    have hv1 : ∑ x : Fin d, v.ofLp x * star (v.ofLp x) = ⟪v, v⟫_ℂ := by
     rw [inner_eq_star_dotProduct, dotProduct]
     refine sum_congr rfl fun x _ => by simp [Pi.star_apply]
    rw [hv1, inner_self_eq_norm_sq_to_K, hv_norm]; simp
   exact_mod_cast hC
  have hval : hS.eigenvalues i = ‖CLM Q hVv‖ ^ 2 := by
   have hC : (hS.eigenvalues i : ℂ) = ((‖CLM Q hVv‖ ^ 2 : ℝ) : ℂ) := by
    have hv_eig : CLM S v = (hS.eigenvalues i : ℂ) • v := by
     apply WithLp.ofLp_injective
     simpa [ofLp_toEuclideanCLM, RCLike.real_smul_eq_coe_smul] using
      hS.mulVec_eigenvectorBasis i
    have h1 : (hS.eigenvalues i : ℂ) = ⟪v, CLM S v⟫_ℂ := by
     rw [hv_eig, inner_smul_right, inner_self_eq_norm_sq_to_K, hv_norm]; simp
    have h2 : ⟪v, CLM S v⟫_ℂ = ⟪hVv, CLM Q hVv⟫_ℂ := by
     have hL : ⟪v, CLM S v⟫_ℂ =
       ∑ p : K, ∑ q : K, ∑ x : Fin d, ∑ y : Fin d,
        star (V p x) * Q p q * V q y * v.ofLp y * star (v.ofLp x) := by
      change ∑ x : Fin d, (CLM S v).ofLp x * star (v.ofLp x) = _
      have hexp : ∀ x : Fin d, (CLM S v).ofLp x * star (v.ofLp x) =
        ∑ y : Fin d, ∑ q : K, ∑ p : K,
         star (V p x) * Q p q * V q y * v.ofLp y * star (v.ofLp x) := by
       intro x
       dsimp only [CLM, S]
       rw [ofLp_toEuclideanCLM, mulVec, dotProduct, Finset.sum_mul]
       refine sum_congr rfl fun y _ => ?_
       rw [mul_apply, Finset.sum_mul, Finset.sum_mul]
       refine sum_congr rfl fun q _ => ?_
       rw [mul_apply, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
       refine sum_congr rfl fun p _ => by rw [ctA]
      simp_rw [hexp]
      have hswap1 : ∀ x : Fin d,
        (∑ y : Fin d, ∑ q : K, ∑ p : K,
         star (V p x) * Q p q * V q y * v.ofLp y * star (v.ofLp x)) =
        ∑ p : K, ∑ q : K, ∑ y : Fin d,
         star (V p x) * Q p q * V q y * v.ofLp y * star (v.ofLp x) := by
       intro x
       rw [sum_comm]
       refine (sum_congr rfl fun q _ => sum_comm).trans ?_
       rw [sum_comm]
      simp_rw [hswap1]
      rw [sum_comm]
      refine sum_congr rfl fun p _ => ?_
      rw [sum_comm]
     have hR : ⟪hVv, CLM Q hVv⟫_ℂ =
       ∑ p : DilK bdA, ∑ q : DilK bdA, ∑ x : Fin d, ∑ y : Fin d,
        star (V p x) * Q p q * V q y * v.ofLp y * star (v.ofLp x) := by
      change ∑ p : DilK bdA, (CLM Q hVv).ofLp p * star (hVv.ofLp p) = _
      refine sum_congr rfl fun p _ => ?_
      dsimp only [CLM, hVv]
      rw [ofLp_toEuclideanCLM, mulVec, dotProduct, Finset.sum_mul]
      refine sum_congr rfl fun q _ => ?_
      simp only [mulVec, dotProduct, star_sum, Finset.mul_sum, Finset.sum_mul]
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by
       rw [star_mul]; ring
     rw [hL, hR]
    rw [h1, h2, proj_inner_eq_norm_sq hQh hQp hVv]
   exact_mod_cast hC
  rw [hval]
  have hle := proj_norm_sq_le hQh hQp hVv
  rw [hVv_norm] at hle
  exact ⟨sq_nonneg _, hle⟩
 have hS_comm_A' : ∀ c ∈ comm A, c * S = S * c := by
  intro c hc
  have hc' : cᴴ ∈ comm A := star_mem hc
  have hVh : Vᴴ * dilRhoA' bdA c = c * Vᴴ := by
   have h1 := congrArg Matrix.conjTranspose (dilRhoA'_mul_dilV bdA hc')
   rw [ctM, ctM, ← dilRhoA'_star,
    ctct] at h1
   exact h1
  dsimp only [S]
  calc
   c * (Vᴴ * Q * V) = (c * Vᴴ) * Q * V := by simp only [mma]
   _ = Vᴴ * (dilRhoA' bdA c * Q) * V := by rw [← hVh]; simp only [mma]
   _ = Vᴴ * Q * (dilRhoA' bdA c * V) := by rw [hQ_comm_A' c hc]; simp only [mma]
   _ = Vᴴ * Q * V * c := by dsimp only [V]; rw [dilRhoA'_mul_dilV bdA hc]; simp only [mma]
 have hS_comm_AB : ∀ x ∈ A, x ∈ B → x * S = S * x := by
  intro x hxA hxB
  have hxA' : xᴴ ∈ A := star_mem hxA
  have hVh : Vᴴ * dRB bdA x = x * Vᴴ := by
   have h1 := congrArg Matrix.conjTranspose (dilRhoB_mul_dilV_of_mem bdA hxA')
   rw [ctM, ctM, ← dilRhoB_star,
    ctct] at h1
   exact h1
  dsimp only [S]
  calc
   x * (Vᴴ * Q * V) = (x * Vᴴ) * Q * V := by simp only [mma]
   _ = Vᴴ * (dRB bdA x * Q) * V := by rw [← hVh]; simp only [mma]
   _ = Vᴴ * Q * (dRB bdA x * V) := by rw [hQ_comm_B x hxB]; simp only [mma]
   _ = Vᴴ * Q * V * x := by dsimp only [V]; rw [dilRhoB_mul_dilV_of_mem bdA hxA]; simp only [mma]
 let invSqrtS : Matrix (Fin d) (Fin d) ℂ :=
  hS.cfc (fun t => if 0 < t then (sqrt t)⁻¹ else 0)
 let Psrc : Matrix (Fin d) (Fin d) ℂ := hS.cfc (fun t => if 0 < t then 1 else 0)
 have hinvSqrtS_herm : invSqrtSᴴ = invSqrtS := (cfc_isHermitian hS _).eq
 let W₀ : Matrix K (Fin d) ℂ := Q * V * invSqrtS
 have hQ_W₀ : Q * W₀ = W₀ := by dsimp only [W₀]; rw [← mma, ← mma, hQp]
 let W : Matrix (Fin m) (Fin d) ℂ := ιQᴴ * W₀
 have hW_star_W : Wᴴ * W = Psrc := by
  calc
   Wᴴ * W = W₀ᴴ * (ιQ * ιQᴴ) * W₀ := by
      dsimp only [W]; simp only [ctM, ctct,
       mma]
   _ = W₀ᴴ * W₀ := by rw [hιQ_mul, mma, hQ_W₀]
   _ = invSqrtS * S * invSqrtS := by
      dsimp only [W₀, S]
      rw [ctM, ctM, hinvSqrtS_herm, hQh.eq]
      calc
       invSqrtS * (Vᴴ * Q) * (Q * V * invSqrtS)
        = invSqrtS * (Vᴴ * (Q * Q) * V) * invSqrtS := by simp only [mma]
       _ = invSqrtS * (Vᴴ * Q * V) * invSqrtS := by rw [hQp]
   _ = Psrc := by
      dsimp only [invSqrtS, Psrc]
      conv_lhs => arg 1; arg 2; rw [← cfc_id hS]
      rw [cfc_mul, cfc_mul]
      refine cfc_congr hS fun i => ?_
      by_cases h0 : 0 < hS.eigenvalues i
      ·
       simp only [if_pos h0, id_eq]
       have hs0 : sqrt (hS.eigenvalues i) ≠ 0 := ne_of_gt (sqrt_pos.mpr h0)
       have hsq : sqrt (hS.eigenvalues i) * sqrt (hS.eigenvalues i) = hS.eigenvalues i :=
        mul_self_sqrt (le_of_lt h0)
       calc
        (sqrt (hS.eigenvalues i))⁻¹ * hS.eigenvalues i * (sqrt (hS.eigenvalues i))⁻¹
         = (sqrt (hS.eigenvalues i))⁻¹ *
           (sqrt (hS.eigenvalues i) * sqrt (hS.eigenvalues i)) *
           (sqrt (hS.eigenvalues i))⁻¹ := by rw [hsq]
        _ = 1 := by field_simp [hs0]
      · simp [h0]
 have hW_src : (Wᴴ * W) * (Wᴴ * W) = Wᴴ * W := by
  rw [hW_star_W]; dsimp only [Psrc]; rw [cfc_mul]
  refine cfc_congr hS fun i => by by_cases h0 : 0 < hS.eigenvalues i <;> simp [h0]
 have hW_Psrc : W * Psrc = W := by
  dsimp only [W, W₀, invSqrtS, Psrc]
  rw [mma, mma, cfc_mul]
  congr 2
  refine cfc_congr hS fun i => by by_cases h0 : 0 < hS.eigenvalues i <;> simp [h0]
 have hW_tgt : (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ := by
  calc
   (W * Wᴴ) * (W * Wᴴ) = (W * (Wᴴ * W)) * Wᴴ := by simp only [mma]
   _ = W * Wᴴ := by rw [hW_star_W, hW_Psrc]
 have htr1S : ((1 - S).trace).re = hsSq ((1 - Q) * V) := by
  rw [hsSq_tr, ctM, ctS,
   conjTranspose_one, hQh.eq]
  have h1Qp : (1 - Q) * (1 - Q) = 1 - Q := by
   rw [msm, mms, mms, m1m, m1m,
    mm1, hQp]; abel
  congr 2
  calc
   (1 : Matrix (Fin d) (Fin d) ℂ) - S = Vᴴ * V - Vᴴ * Q * V := by rw [dilV_star_mul]
   _ = Vᴴ * ((1 - Q) * (1 - Q)) * V := by
      rw [h1Qp, mms, mm1, msm]
   _ = Vᴴ * (1 - Q) * ((1 - Q) * V) := by simp only [mma]
 have h1S_cfc : (1 : Matrix (Fin d) (Fin d) ℂ) - S = hS.cfc (fun t => 1 - t) := by
  rw [← cfc_sub hS (fun _ => 1) (fun t => t), cfc_one hS,
   show hS.cfc (fun t => t) = S from cfc_id hS]
 have hW_src_tr : ((1 - Wᴴ * W).trace).re ≤ 2 * ε ^ 2 * (d : ℝ) := by
  rw [hW_star_W]
  have h1 : (1 : Matrix (Fin d) (Fin d) ℂ) - Psrc = hS.cfc (fun t => if 0 < t then 0 else 1) := by
   dsimp only [Psrc]
   rw [← cfc_one hS, cfc_sub]
   refine cfc_congr hS fun i => by by_cases h0 : 0 < hS.eigenvalues i <;> simp [h0]
  rw [h1, trace_cfc, re_sum]
  calc
   (∑ i : Fin d, ((if 0 < hS.eigenvalues i then (0 : ℝ) else 1 : ℝ) : ℂ).re)
    ≤ ∑ i : Fin d, (1 - hS.eigenvalues i) := by
     refine sum_le_sum fun i _ => ?_
     rcases hS_eig i with ⟨h0, h1'⟩
     by_cases hpos : 0 < hS.eigenvalues i
     · simp [hpos]; linarith
     ·
      have heq0 : hS.eigenvalues i = 0 := le_antisymm (not_lt.mp hpos) h0
      simp [heq0]
   _ = ((1 - S).trace).re := by rw [h1S_cfc, trace_cfc, re_sum]; simp
   _ = hsSq ((1 - Q) * V) := htr1S
   _ ≤ 2 * ε ^ 2 * (d : ℝ) := hhs_1Q_V
 have hW_tgt_tr : ((1 - W * Wᴴ).trace).re ≤ 4 * ε ^ 2 * (d : ℝ) := by
  have htr_eq : (W * Wᴴ).trace = (Wᴴ * W).trace := trace_mul_comm _ _
  have h1 : ((1 - W * Wᴴ).trace).re = (m : ℝ) - (d : ℝ) + ((1 - Wᴴ * W).trace).re := by
   rw [trace_sub, trace_sub, htr_eq, trace_one, trace_one,
    card_fin, card_fin, sub_re, sub_re]; simp
  rw [h1]
  have hm_le : (m : ℝ) - (d : ℝ) ≤ 2 * ε ^ 2 * (d : ℝ) := (le_abs_self _).trans hm_diff
  linarith
 have hW₀_sub_V_norm : hsN (W₀ - V) ≤ 2 * ε * sqrt (d : ℝ) := by
  have hW₀_sub_V : hsSq (W₀ - V) ≤ 4 * ε ^ 2 * (d : ℝ) := by
   have hsplit : W₀ - V = (W₀ - Q * V) - (1 - Q) * V := by
    rw [msm, m1m]; abel
   have horth : ((W₀ - Q * V)ᴴ * ((1 - Q) * V)).trace = 0 := by
    have hQ1 : Q * (1 - Q) = 0 := by rw [mms, mm1, hQp, sub_self]
    have hQfac : W₀ - Q * V = Q * (W₀ - Q * V) := by
     rw [mms, hQ_W₀, ← mma, hQp]
    conv_lhs => rw [hQfac]
    rw [ctM, hQh.eq]
    calc
     ((W₀ - Q * V)ᴴ * Q * ((1 - Q) * V)).trace
      = ((W₀ - Q * V)ᴴ * (Q * (1 - Q)) * V).trace := by simp only [mma]
     _ = (0 : ℂ) := by rw [hQ1, Matrix.mul_zero, Matrix.zero_mul, trace_zero]
   have hpyth : hsSq (W₀ - V) = hsSq (W₀ - Q * V) + hsSq ((1 - Q) * V) := by
    have hC : ((hsSq (W₀ - V) : ℝ) : ℂ) =
      ((hsSq (W₀ - Q * V) : ℝ) : ℂ) + ((hsSq ((1 - Q) * V) : ℝ) : ℂ) := by
     rw [hsSq_trC, hsSq_trC, hsSq_trC, hsplit,
      ctS, msm, mms, mms,
      trace_sub, trace_sub, trace_sub, horth]
     have horth' : (((1 - Q) * V)ᴴ * (W₀ - Q * V)).trace = 0 := by
      have hc := congrArg star horth
      rw [star_zero, ← trace_conjTranspose, ctM,
       ctct] at hc
      exact hc
     rw [mms, trace_sub, horth']; ring
    exact_mod_cast hC
   have hterm1 : hsSq (W₀ - Q * V) ≤ 2 * ε ^ 2 * (d : ℝ) := by
    have hfact : W₀ - Q * V = Q * V * (invSqrtS - 1) := by
     dsimp only [W₀]; rw [mms, mm1]
    have hsq_eq : (W₀ - Q * V)ᴴ * (W₀ - Q * V) =
      hS.cfc (fun t => ((if 0 < t then (sqrt t)⁻¹ else 0) - 1) ^ 2 * t) := by
     rw [hfact, ctM, ctM, ctS,
      conjTranspose_one, hinvSqrtS_herm, hQh.eq]
     calc
      (invSqrtS - 1) * (Vᴴ * Q) * (Q * V * (invSqrtS - 1))
       = (invSqrtS - 1) * (Vᴴ * (Q * Q) * V) * (invSqrtS - 1) := by simp only [mma]
      _ = (invSqrtS - 1) * S * (invSqrtS - 1) := by rw [hQp]
      _ = hS.cfc (fun t => ((if 0 < t then (sqrt t)⁻¹ else 0) - 1) ^ 2 * t) := by
         have hsub1 : invSqrtS - 1 = hS.cfc (fun t => (if 0 < t then (sqrt t)⁻¹ else 0) - 1) := by
          dsimp only [invSqrtS]; rw [← cfc_one hS, cfc_sub]
         rw [hsub1]
         conv_lhs => arg 1; arg 2; rw [← cfc_id hS]
         rw [cfc_mul, cfc_mul]
         refine cfc_congr hS fun i => by simp only [id_eq]; ring
    rw [hsSq_tr, hsq_eq, trace_cfc, re_sum]
    calc
     ∑ i : Fin d, ((((if 0 < hS.eigenvalues i then (sqrt (hS.eigenvalues i))⁻¹ else 0) - 1) ^ 2 *
        hS.eigenvalues i : ℝ) : ℂ).re
      ≤ ∑ i : Fin d, (1 - hS.eigenvalues i) := by
       refine sum_le_sum fun i _ => ?_
       simp only [Complex.ofReal_re]
       rcases hS_eig i with ⟨h0, h1'⟩
       by_cases hpos : 0 < hS.eigenvalues i
       ·
        rw [if_pos hpos]
        have hs_nn : 0 ≤ sqrt (hS.eigenvalues i) := sqrt_nonneg _
        have hs_le1 : sqrt (hS.eigenvalues i) ≤ 1 := by
         rw [← Real.sqrt_one]; exact sqrt_le_sqrt h1'
        have hsq : sqrt (hS.eigenvalues i) * sqrt (hS.eigenvalues i) = hS.eigenvalues i :=
         mul_self_sqrt h0
        have hs0 : sqrt (hS.eigenvalues i) ≠ 0 := ne_of_gt (sqrt_pos.mpr hpos)
        have heq : ((sqrt (hS.eigenvalues i))⁻¹ - 1) ^ 2 * hS.eigenvalues i =
          (1 - sqrt (hS.eigenvalues i)) ^ 2 := by
         field_simp [hs0]; nlinarith
        rw [heq]; nlinarith
       ·
        have heq0 : hS.eigenvalues i = 0 := le_antisymm (not_lt.mp hpos) h0
        simp [heq0]
     _ = ((1 - S).trace).re := by rw [h1S_cfc, trace_cfc, re_sum]; simp
     _ = hsSq ((1 - Q) * V) := htr1S
     _ ≤ 2 * ε ^ 2 * (d : ℝ) := hhs_1Q_V
   linarith
  have h1 := sqrt_le_sqrt hW₀_sub_V
  have hrhs : sqrt (4 * ε ^ 2 * (d : ℝ)) = 2 * ε * sqrt (d : ℝ) := by
   have : 4 * ε ^ 2 * (d : ℝ) = (2 * ε) ^ 2 * (d : ℝ) := by ring
   rw [this, sqrt_mul (sq_nonneg _), sqrt_sq (by linarith)]
  rwa [← hrhs]
 refine ⟨W, hW_src, hW_tgt, hW_src_tr, hW_tgt_tr, ?_, ?_, ?_⟩
 ·
  intro c hc
  have hinv_comm : c * invSqrtS = invSqrtS * c := cfc_commute hS c (hS_comm_A' c hc) _
  dsimp only [πA', W, W₀]
  calc
   (ιQᴴ * dilRhoA' bdA c * ιQ) * (ιQᴴ * (Q * V * invSqrtS))
    = ιQᴴ * (dilRhoA' bdA c * (Q * Q) * V * invSqrtS) := by rw [← hιQ_mul]; simp only [mma]
   _ = ιQᴴ * (Q * (dilRhoA' bdA c * V) * invSqrtS) := by
      rw [hQp, hQ_comm_A' c hc]; simp only [mma]
   _ = ιQᴴ * (Q * V * (c * invSqrtS)) := by dsimp only [V]; rw [dilRhoA'_mul_dilV bdA hc]; simp only [mma]
   _ = ιQᴴ * (Q * V * invSqrtS) * c := by rw [hinv_comm]; simp only [mma]
 ·
  intro x hxA hxB
  have hinv_comm : x * invSqrtS = invSqrtS * x := cfc_commute hS x (hS_comm_AB x hxA hxB) _
  dsimp only [πB, W, W₀]
  calc
   (ιQᴴ * dRB bdA x * ιQ) * (ιQᴴ * (Q * V * invSqrtS))
    = ιQᴴ * (dRB bdA x * (Q * Q) * V * invSqrtS) := by rw [← hιQ_mul]; simp only [mma]
   _ = ιQᴴ * (Q * (dRB bdA x * V) * invSqrtS) := by
      rw [hQp, hQ_comm_B x hxB]; simp only [mma]
   _ = ιQᴴ * (Q * V * (x * invSqrtS)) := by dsimp only [V]; rw [dilRhoB_mul_dilV_of_mem bdA hxA]; simp only [mma]
   _ = ιQᴴ * (Q * V * invSqrtS) * x := by rw [hinv_comm]; simp only [mma]
 ·
  intro b hb hbn
  have hdiff : πB b * W - W * b = ιQᴴ * (dRB bdA b * W₀ - W₀ * b) := by
   dsimp only [πB, W]
   rw [mms, mma, mma, ← mma ιQ, hιQ_mul, hQ_W₀]
   simp only [mma]
  have hsplit : dRB bdA b * W₀ - W₀ * b =
    dRB bdA b * (W₀ - V) + (dRB bdA b * V - V * b) - (W₀ - V) * b := by
   rw [mms, msm]; abel
  have h1 : hsN (dRB bdA b * (W₀ - V)) ≤ 2 * ε * sqrt (d : ℝ) := by
   calc
    hsN (dRB bdA b * (W₀ - V))
     ≤ ‖CLM (dRB bdA b)‖ * hsN (W₀ - V) := hsN_mulL _ _
    _ ≤ 1 * (2 * ε * sqrt (d : ℝ)) :=
      mul_le_mul ((dilRhoB_opNorm bdA b).trans hbn) hW₀_sub_V_norm (hsN_nn _) zero_le_one
    _ = 2 * ε * sqrt (d : ℝ) := one_mul _
  have h2 : hsN (dRB bdA b * V - V * b) ≤ 2 * ε * sqrt (d : ℝ) := by
   have hsq : hsSq (dRB bdA b * V - V * b) ≤ (2 * ε * sqrt (d : ℝ)) ^ 2 := by
    rw [hsSq_dilRhoB_mul_dilV_sub, mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg d)]
    have hinc_b := hinc b hb hbn
    nlinarith [sq_nonneg ε, Nat.cast_nonneg (α := ℝ) d]
   have hrt := sqrt_le_sqrt hsq
   rwa [sqrt_sq (by positivity)] at hrt
  have h3 : hsN ((W₀ - V) * b) ≤ 2 * ε * sqrt (d : ℝ) := by
   calc
    hsN ((W₀ - V) * b)
     ≤ ‖CLM b‖ * hsN (W₀ - V) := hsN_mulR _ _
    _ ≤ 1 * (2 * ε * sqrt (d : ℝ)) :=
      mul_le_mul hbn hW₀_sub_V_norm (hsN_nn _) zero_le_one
    _ = 2 * ε * sqrt (d : ℝ) := one_mul _
  calc
   hsN (πB b * W - W * b)
    = hsN (ιQᴴ * (dRB bdA b * W₀ - W₀ * b)) := by rw [hdiff]
   _ ≤ hsN (dRB bdA b * W₀ - W₀ * b) := sqrt_le_sqrt (hsSq_isometry_mul_le ιQ hιQ_star _)
   _ = hsN (dRB bdA b * (W₀ - V) + (dRB bdA b * V - V * b) - (W₀ - V) * b) := by rw [hsplit]
   _ ≤ hsN (dRB bdA b * (W₀ - V) + (dRB bdA b * V - V * b)) + hsN ((W₀ - V) * b) := hsN_sub _ _
   _ ≤ hsN (dRB bdA b * (W₀ - V)) + hsN (dRB bdA b * V - V * b) + hsN ((W₀ - V) * b) := by
      linarith [hsN_add (dRB bdA b * (W₀ - V)) (dRB bdA b * V - V * b)]
   _ ≤ 6 * ε * sqrt (d : ℝ) := by linarith
lemma bratteli_A_mult {d m : ℕ}
  {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdA : BDec A) {ε : ℝ}
  (πA' : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin m) (Fin m) ℂ)
  (r' : Fin bdA.t → ℕ)
  (W : Matrix (Fin m) (Fin d) ℂ)
  (hπA'_one : πA' 1 = 1)
  (hπA'_add : ∀ c₁ c₂, πA' (c₁ + c₂) = πA' c₁ + πA' c₂)
  (hπA'_smul : ∀ (α : ℂ) c, πA' (α • c) = α • πA' c)
  (hπA'_mul : ∀ c₁ c₂, c₁ ∈ comm A → c₂ ∈ comm A → πA' (c₁ * c₂) = πA' c₁ * πA' c₂)
  (hπA'_star : ∀ c, πA' cᴴ = (πA' c)ᴴ)
  (hAhat_tr : ∀ j : Fin bdA.t, (πA' (cPr bdA j)).trace = ((r' j * bdA.s j : ℕ) : ℂ))
  (hW_src : (Wᴴ * W) * (Wᴴ * W) = Wᴴ * W)
  (hW_src_tr : ((1 - Wᴴ * W).trace).re ≤ 2 * ε ^ 2 * (d : ℝ))
  (hW_comm_A' : ∀ c ∈ comm A, πA' c * W = W * c)
  (hm_diff : |(m : ℝ) - (d : ℝ)| ≤ 2 * ε ^ 2 * (d : ℝ)) :
  ∑ j : Fin bdA.t, (bdA.s j : ℝ) * |(r' j : ℝ) - (bdA.r j : ℝ)| ≤ 6 * ε ^ 2 * (d : ℝ) := by
 have hrank_le : (Module.finrank ℂ (LinearMap.range (mulVecLin W)) : ℝ) ≤
   ∑ j : Fin bdA.t, min ((bdA.r j : ℝ) * (bdA.s j : ℝ)) ((r' j : ℝ) * (bdA.s j : ℝ)) := by
  have h1 := finrank_range_le_sum_proj W (cPr bdA) (sum_cPr bdA)
  have h2 : ∀ j : Fin bdA.t,
    (Module.finrank ℂ (LinearMap.range (mulVecLin (W * cPr bdA j))) : ℝ) ≤
     min ((bdA.r j : ℝ) * (bdA.s j : ℝ)) ((r' j : ℝ) * (bdA.s j : ℝ)) := by
   intro j
   have hle := finrank_range_mul_proj_le W (cPr bdA j) (πA' (cPr bdA j))
    (hW_comm_A' _ (cPr_comm bdA j)).symm
   have htr1 : (Module.finrank ℂ (LinearMap.range (mulVecLin (cPr bdA j))) : ℝ) =
     (bdA.r j : ℝ) * (bdA.s j : ℝ) := by
    have ht := proj_trace_eq_finrank_mulVecLin (cPr_herm bdA j)
     (by rw [cPr_mul]; simp)
    have ht' : (cPr bdA j).trace = ((bdA.r j * bdA.s j : ℕ) : ℂ) := by
     rw [← sum_matUnitA_diag bdA j, trace_sum]
     simp_rw [trace_matUnitA_diag]; simp [sum_const, nsmul_eq_mul, Nat.cast_mul]
    have hre := congrArg Complex.re (ht.symm.trans ht')
    simpa [Nat.cast_mul] using hre
   have htr2 : (Module.finrank ℂ (LinearMap.range (mulVecLin (πA' (cPr bdA j)))) : ℝ) =
     (r' j : ℝ) * (bdA.s j : ℝ) := by
    have hPh : (πA' (cPr bdA j)).IsHermitian := by
     dsimp only [IsHermitian]; rw [← hπA'_star, cPr_herm]
    have hPp : πA' (cPr bdA j) * πA' (cPr bdA j) = πA' (cPr bdA j) := by
     rw [← hπA'_mul _ _ (cPr_comm bdA j) (cPr_comm bdA j),
      cPr_mul]; simp
    have ht := proj_trace_eq_finrank_mulVecLin hPh hPp
    have hre := congrArg Complex.re (ht.symm.trans (hAhat_tr j))
    simpa [Nat.cast_mul] using hre
   have hle_R : (Module.finrank ℂ (LinearMap.range (mulVecLin (W * cPr bdA j))) : ℝ) ≤
     min (Module.finrank ℂ (LinearMap.range (mulVecLin (cPr bdA j))) : ℝ)
      (Module.finrank ℂ (LinearMap.range (mulVecLin (πA' (cPr bdA j)))) : ℝ) := by
    exact_mod_cast hle
   rwa [htr1, htr2] at hle_R
  exact (Nat.cast_le.mpr h1).trans (by rw [Nat.cast_sum]; exact sum_le_sum fun j _ => h2 j)
 obtain ⟨Pker, hPker_h, hPker_p, hW_Pker, hPker_tr⟩ := exists_ker_proj W
 have hker_le : ((Pker.trace).re : ℝ) ≤ 2 * ε ^ 2 * (d : ℝ) := by
  have hPker_eq : Pker = (1 - Wᴴ * W) * Pker := by
   rw [msm, m1m, mma, hW_Pker, Matrix.mul_zero, sub_zero]
  have h1Ph : (1 - Wᴴ * W)ᴴ = 1 - Wᴴ * W := by
   rw [ctS, conjTranspose_one, ctM,
    ctct]
  have h1Pp : (1 - Wᴴ * W) * (1 - Wᴴ * W) = 1 - Wᴴ * W := by
   rw [msm, mms, mms, m1m, m1m,
    mm1, hW_src]; abel
  calc
   ((Pker.trace).re : ℝ) = hsSq Pker := by rw [hsSq_tr, hPker_h.eq, hPker_p]
   _ = hsSq ((1 - Wᴴ * W) * Pker) := by conv_lhs => rw [hPker_eq]
   _ = hsSq (Pker * (1 - Wᴴ * W)) := by
      rw [← hsSq_ct, ctM, hPker_h.eq, h1Ph]
   _ ≤ hsSq (1 - Wᴴ * W) := hsSq_proj_mul_le Pker hPker_h.eq hPker_p (1 - Wᴴ * W)
   _ = ((1 - Wᴴ * W).trace).re := by rw [hsSq_tr, h1Ph, h1Pp]
   _ ≤ 2 * ε ^ 2 * (d : ℝ) := hW_src_tr
 have hrk_null : (Module.finrank ℂ (LinearMap.range (mulVecLin W)) : ℝ) +
   ((Pker.trace).re : ℝ) = (d : ℝ) := by
  rw [hPker_tr]
  have h := LinearMap.finrank_range_add_finrank_ker (mulVecLin W)
  rw [Module.finrank_fin_fun] at h
  exact_mod_cast h
 have hsum_d : ∑ j : Fin bdA.t, (bdA.r j : ℝ) * (bdA.s j : ℝ) = (d : ℝ) := by
  have h1 : ∑ j : Fin bdA.t, (cPr bdA j).trace = (d : ℂ) := by
   rw [← trace_sum, sum_cPr, trace_one, card_fin]
  have hterm : ∀ j : Fin bdA.t, (cPr bdA j).trace = ((bdA.r j * bdA.s j : ℕ) : ℂ) := by
   intro j; rw [← sum_matUnitA_diag bdA j, trace_sum]
   simp_rw [trace_matUnitA_diag]; simp [sum_const, nsmul_eq_mul, Nat.cast_mul]
  simp_rw [hterm] at h1
  have hre := congrArg Complex.re h1
  simpa [re_sum, Nat.cast_mul] using hre
 have hsum_m : ∑ j : Fin bdA.t, (r' j : ℝ) * (bdA.s j : ℝ) = (m : ℝ) := by
  have h1 : ∑ j : Fin bdA.t, (πA' (cPr bdA j)).trace = (m : ℂ) := by
   have hsum_π : ∀ {α : Type} [DecidableEq α] (s : Finset α) (f : α → Matrix (Fin d) (Fin d) ℂ),
     πA' (∑ a ∈ s, f a) = ∑ a ∈ s, πA' (f a) := by
    intro α _ s f
    induction s using induction_on with
    | empty => have := hπA'_smul 0 0; simpa using this
    | insert a s ha ih => rw [sum_insert ha, hπA'_add, ih, sum_insert ha]
   rw [← trace_sum, ← hsum_π, sum_cPr, hπA'_one, trace_one, card_fin]
  simp_rw [hAhat_tr] at h1
  have hre := congrArg Complex.re h1
  simpa [re_sum, Nat.cast_mul] using hre
 have habs_eq : ∑ j : Fin bdA.t, (bdA.s j : ℝ) * |(r' j : ℝ) - (bdA.r j : ℝ)| =
   (m : ℝ) + (d : ℝ) -
    2 * ∑ j : Fin bdA.t, min ((bdA.r j : ℝ) * (bdA.s j : ℝ)) ((r' j : ℝ) * (bdA.s j : ℝ)) := by
  have hterm : ∀ j : Fin bdA.t,
    (bdA.s j : ℝ) * |(r' j : ℝ) - (bdA.r j : ℝ)| =
     (r' j : ℝ) * (bdA.s j : ℝ) + (bdA.r j : ℝ) * (bdA.s j : ℝ) -
      2 * min ((bdA.r j : ℝ) * (bdA.s j : ℝ)) ((r' j : ℝ) * (bdA.s j : ℝ)) := by
   intro j
   have hs_nn : (0 : ℝ) ≤ (bdA.s j : ℝ) := Nat.cast_nonneg _
   by_cases hle : (bdA.r j : ℝ) ≤ (r' j : ℝ)
   ·
    have hle' := mul_le_mul_of_nonneg_right hle hs_nn
    rw [abs_of_nonneg (sub_nonneg.mpr hle), min_eq_left hle']; ring
   ·
    push Not at hle
    have hle' := mul_le_mul_of_nonneg_right (le_of_lt hle) hs_nn
    rw [abs_of_neg (sub_neg.mpr hle), min_eq_right hle']; ring
  simp_rw [hterm, sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
   hsum_m, hsum_d]
 have hm_le : (m : ℝ) - (d : ℝ) ≤ 2 * ε ^ 2 * (d : ℝ) := (le_abs_self _).trans hm_diff
 linarith
lemma bratteli_B_mult {d m : ℕ}
  {B A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdB : BDec B) (bdA : BDec A)
  {ε : ℝ}
  (hinc : ∀ b ∈ B, ‖CLM b‖ ≤ 1 → hsSq (b - cExp A b) ≤ ε ^ 2 * (d : ℝ))
  {Q : Matrix (DilK bdA) (DilK bdA) ℂ}
  (hQh : Q.IsHermitian) (hQp : Q * Q = Q)
  (hQ_comm_B : ∀ b ∈ B, dRB bdA b * Q = Q * dRB bdA b)
  (hhs_1Q_V : hsSq ((1 - Q) * dV bdA) ≤ 2 * ε ^ 2 * (d : ℝ))
  {ιQ : Matrix (DilK bdA) (Fin m) ℂ}
  (hιQ_star : ιQᴴ * ιQ = 1) (hιQ_mul : ιQ * ιQᴴ = Q)
  (hm_diff : |(m : ℝ) - (d : ℝ)| ≤ 2 * ε ^ 2 * (d : ℝ))
  (πB : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin m) (Fin m) ℂ)
  (hπB_def : ∀ x, πB x = ιQᴴ * dRB bdA x * ιQ)
  (hπB_one : πB 1 = 1)
  (hπB_add : ∀ x y, πB (x + y) = πB x + πB y)
  (hπB_smul : ∀ (α : ℂ) x, πB (α • x) = α • πB x)
  (hπB_mul : ∀ x y, x ∈ B → y ∈ B → πB (x * y) = πB x * πB y)
  (hπB_star : ∀ x, πB xᴴ = (πB x)ᴴ)
  (q' : Fin bdB.t → ℕ)
  (hBhat_tr : ∀ i : Fin bdB.t, (πB (cPr bdB i)).trace = ((bdB.r i * q' i : ℕ) : ℂ)) :
  ∑ i : Fin bdB.t, (bdB.r i : ℝ) * |(q' i : ℝ) - (bdB.s i : ℝ)| ≤ 8 * ε ^ 2 * (d : ℝ) := by
 let V := dV bdA
 let T : Matrix (Fin m) (Fin d) ℂ :=
  ∑ i : Fin bdB.t, πB (cPr bdB i) * (ιQᴴ * V) * cPr bdB i
 have hT_int : ∀ i : Fin bdB.t, T * cPr bdB i = πB (cPr bdB i) * T := by
  intro i
  dsimp only [T]
  rw [Matrix.sum_mul, Matrix.mul_sum, sum_eq_single i, sum_eq_single i]
  ·
   simp only [mma, cPr_mul, ↓reduceIte]
   rw [← mma (πB (cPr bdB i)) (πB (cPr bdB i)),
    ← hπB_mul _ _ (cPr_mem bdB i) (cPr_mem bdB i), cPr_mul, if_pos rfl]
  ·
   intro j _ hji
   rw [← mma, ← mma,
    ← hπB_mul _ _ (cPr_mem bdB i) (cPr_mem bdB j),
    cPr_mul, if_neg hji.symm, show πB 0 = 0 by simpa using hπB_smul 0 0,
    Matrix.zero_mul, Matrix.zero_mul]
  · intro h; exact absurd (mem_univ i) h
  ·
   intro j _ hji
   rw [mma, cPr_mul, if_neg hji, Matrix.mul_zero]
  · intro h; exact absurd (mem_univ i) h
 have hT_diff : hsSq (T - ιQᴴ * V) ≤ ε ^ 2 * (d : ℝ) := by
  let X (i : Fin bdB.t) : Matrix (Fin m) (Fin d) ℂ :=
   (1 - πB (cPr bdB i)) * (ιQᴴ * V) * cPr bdB i
  have hdiff_eq : ιQᴴ * V - T = ∑ i : Fin bdB.t, X i := by
   have h1 : ιQᴴ * V = ∑ i : Fin bdB.t, (ιQᴴ * V) * cPr bdB i := by
    rw [← Matrix.mul_sum, sum_cPr, mm1]
   conv_lhs => arg 1; rw [h1]
   dsimp only [T, X]
   rw [← sum_sub_distrib]
   refine sum_congr rfl fun i _ => by rw [msm, m1m, msm]
  rw [show hsSq (T - ιQᴴ * V) = hsSq (ιQᴴ * V - T) by rw [← hsSq_neg, neg_sub], hdiff_eq]
  have hpyth : hsSq (∑ i : Fin bdB.t, X i) = ∑ i : Fin bdB.t, hsSq (X i) := by
   rw [hsSq_tr, conjTranspose_sum, Matrix.sum_mul, trace_sum, re_sum]
   refine sum_congr rfl fun i _ => ?_
   rw [Matrix.mul_sum, trace_sum, re_sum, sum_eq_single i]
   · rw [hsSq_tr]
   ·
    intro j _ hji
    have h0 : ((X i)ᴴ * X j).trace = 0 := by
     dsimp only [X]
     calc
      (((1 - πB (cPr bdB i)) * (ιQᴴ * V) * cPr bdB i)ᴴ *
        ((1 - πB (cPr bdB j)) * (ιQᴴ * V) * cPr bdB j)).trace
       = (cPr bdB i * (((1 - πB (cPr bdB i)) * (ιQᴴ * V))ᴴ *
         ((1 - πB (cPr bdB j)) * (ιQᴴ * V))) * cPr bdB j).trace := by
         rw [ctM, cPr_herm]; simp only [mma]
      _ = (cPr bdB j * cPr bdB i *
         (((1 - πB (cPr bdB i)) * (ιQᴴ * V))ᴴ *
          ((1 - πB (cPr bdB j)) * (ιQᴴ * V)))).trace := by
         rw [trace_mul_comm]; simp only [mma]
      _ = (0 : ℂ) := by rw [cPr_mul, if_neg hji, Matrix.zero_mul, trace_zero]
    rw [h0, zero_re]
   · intro h; exact absurd (mem_univ i) h
  rw [hpyth]
  have hterm : ∀ i : Fin bdB.t,
    hsSq (X i) ≤ hsSq (cPr bdB i - cExp A (cPr bdB i)) := by
   intro i
   let w := cPr bdB i
   have hwB : w ∈ B := cPr_mem bdB i
   have hwh : wᴴ = w := cPr_herm bdB i
   have hwp : w * w = w := by dsimp only [w]; rw [cPr_mul]; simp
   have h1ρw_h : (1 - dRB bdA w)ᴴ = 1 - dRB bdA w := by
    rw [ctS, conjTranspose_one, ← dilRhoB_star, hwh]
   have h1ρw_p : (1 - dRB bdA w) * (1 - dRB bdA w) = 1 - dRB bdA w := by
    rw [msm, mms, mms, m1m, m1m,
     mm1, ← dilRhoB_mul, hwp]; abel
   have hQ_1ρw : Q * (1 - dRB bdA w) = (1 - dRB bdA w) * Q := by
    rw [mms, msm, mm1, m1m, hQ_comm_B w hwB]
   have hXi_eq : hsSq (X i) = hsSq (Q * ((1 - dRB bdA w) * V * w)) := by
    rw [hsSq_tr, hsSq_tr]
    have hι1 : ιQ * (1 - πB w) * ιQᴴ = Q * (1 - dRB bdA w) := by
     rw [hπB_def w, mms, mm1, msm, hιQ_mul]
     calc
      Q - ιQ * (ιQᴴ * dRB bdA w * ιQ) * ιQᴴ
       = Q - (ιQ * ιQᴴ) * dRB bdA w * (ιQ * ιQᴴ) := by simp only [mma]
      _ = Q - Q * (dRB bdA w * Q) := by rw [hιQ_mul, mma]
      _ = Q - Q * (Q * dRB bdA w) := by rw [hQ_comm_B w hwB]
      _ = Q - (Q * Q) * dRB bdA w := by rw [← mma Q Q]
      _ = Q * (1 - dRB bdA w) := by rw [hQp, mms, mm1]
    have hmid : Q * (1 - dRB bdA w) =
      (1 - dRB bdA w) * (Q * Q) * (1 - dRB bdA w) := by
     calc
      Q * (1 - dRB bdA w)
       = Q * ((1 - dRB bdA w) * (1 - dRB bdA w)) := by rw [h1ρw_p]
      _ = (Q * (1 - dRB bdA w)) * (1 - dRB bdA w) := by rw [← mma]
      _ = ((1 - dRB bdA w) * Q) * (1 - dRB bdA w) := by rw [hQ_1ρw]
      _ = (1 - dRB bdA w) * (Q * Q) * (1 - dRB bdA w) := by rw [hQp]
    have h1πh : (1 - πB w)ᴴ = 1 - πB w := by
     rw [ctS, conjTranspose_one, ← hπB_star, hwh]
    have h1πp : (1 - πB w) * (1 - πB w) = 1 - πB w := by
     rw [msm, mms, mms, m1m, m1m,
      mm1, ← hπB_mul _ _ hwB hwB, hwp]; abel
    congr 2
    dsimp only [X]
    calc
     ((1 - πB w) * (ιQᴴ * V) * w)ᴴ * ((1 - πB w) * (ιQᴴ * V) * w)
      = w * Vᴴ * (ιQ * ((1 - πB w) * (1 - πB w)) * ιQᴴ) * V * w := by
        simp only [ctM, ctct,
         hwh, h1πh, mma]
     _ = w * Vᴴ * (Q * (1 - dRB bdA w)) * V * w := by rw [h1πp, hι1]
     _ = w * Vᴴ * ((1 - dRB bdA w) * (Q * Q) * (1 - dRB bdA w)) * V * w := by
        rw [hmid]
     _ = (Q * ((1 - dRB bdA w) * V * w))ᴴ * (Q * ((1 - dRB bdA w) * V * w)) := by
        simp only [ctM, hQh.eq, h1ρw_h, hwh, mma]
   have hstep1 : hsSq (X i) ≤ hsSq ((1 - dRB bdA w) * V * w) := by
    rw [hXi_eq]; exact hsSq_proj_mul_le Q hQh.eq hQp _
   have hstep2 : hsSq ((1 - dRB bdA w) * V * w) = hsSq (w - cExp A w) := by
    have hL : hsSq ((1 - dRB bdA w) * V * w) = (w.trace).re - ((w * cExp A w).trace).re := by
     rw [hsSq_tr]
     have h1 : ((1 - dRB bdA w) * V * w)ᴴ * ((1 - dRB bdA w) * V * w) =
       w * (1 - cExp A w) * w := by
      calc
       ((1 - dRB bdA w) * V * w)ᴴ * ((1 - dRB bdA w) * V * w)
        = w * (Vᴴ * ((1 - dRB bdA w) * (1 - dRB bdA w)) * V) * w := by
          simp only [ctM, h1ρw_h, hwh, mma]
       _ = w * (Vᴴ * V - Vᴴ * dRB bdA w * V) * w := by
          rw [h1ρw_p, mms, mm1, msm]
       _ = w * (1 - cExp A w) * w := by rw [dilV_star_mul, dilV_star_dilRhoB_dilV]
     rw [h1, mms, mm1, msm, hwp, trace_sub,
      sub_re]
     congr 2
     calc
      (w * cExp A w * w).trace = (w * (w * cExp A w)).trace := trace_mul_comm _ _
      _ = (w * cExp A w).trace := by rw [← mma, hwp]
    have hR : hsSq (w - cExp A w) = (w.trace).re - ((w * cExp A w).trace).re := by
     have hpyth_w := hsSq_eq_hsSq_condExp_add A w
     have hw_sq : hsSq w = (w.trace).re := by rw [hsSq_tr, hwh, hwp]
     have hce_sq : hsSq (cExp A w) = ((w * cExp A w).trace).re := by
      rw [hsSq_tr, condExp_inner_eq A w (condExp_mem A w), hwh]
     linarith
    rw [hL, hR]
   exact hstep1.trans_eq hstep2
  exact (sum_le_sum fun i _ => hterm i).trans (sum_hsSq_centralProj_sub_condExp_le bdB hinc)
 have hrank_le : (Module.finrank ℂ (LinearMap.range (mulVecLin T)) : ℝ) ≤
   ∑ i : Fin bdB.t, min ((bdB.r i : ℝ) * (bdB.s i : ℝ)) ((bdB.r i : ℝ) * (q' i : ℝ)) := by
  have h1 := finrank_range_le_sum_proj T (cPr bdB) (sum_cPr bdB)
  have h2 : ∀ i : Fin bdB.t,
    (Module.finrank ℂ (LinearMap.range (mulVecLin (T * cPr bdB i))) : ℝ) ≤
     min ((bdB.r i : ℝ) * (bdB.s i : ℝ)) ((bdB.r i : ℝ) * (q' i : ℝ)) := by
   intro i
   have hle := finrank_range_mul_proj_le T (cPr bdB i) (πB (cPr bdB i)) (hT_int i)
   have htr1 : (Module.finrank ℂ (LinearMap.range (mulVecLin (cPr bdB i))) : ℝ) =
     (bdB.r i : ℝ) * (bdB.s i : ℝ) := by
    have ht := proj_trace_eq_finrank_mulVecLin (cPr_herm bdB i)
     (by rw [cPr_mul]; simp)
    have ht' : (cPr bdB i).trace = ((bdB.r i * bdB.s i : ℕ) : ℂ) := by
     rw [← sum_matUnitA_diag bdB i, trace_sum]
     simp_rw [trace_matUnitA_diag]; simp [sum_const, nsmul_eq_mul, Nat.cast_mul]
    have hre := congrArg Complex.re (ht.symm.trans ht')
    simpa [Nat.cast_mul] using hre
   have htr2 : (Module.finrank ℂ (LinearMap.range (mulVecLin (πB (cPr bdB i)))) : ℝ) =
     (bdB.r i : ℝ) * (q' i : ℝ) := by
    have hPh : (πB (cPr bdB i)).IsHermitian := by
     dsimp only [IsHermitian]; rw [← hπB_star, cPr_herm]
    have hPp : πB (cPr bdB i) * πB (cPr bdB i) = πB (cPr bdB i) := by
     rw [← hπB_mul _ _ (cPr_mem bdB i) (cPr_mem bdB i),
      cPr_mul]; simp
    have ht := proj_trace_eq_finrank_mulVecLin hPh hPp
    have hre := congrArg Complex.re (ht.symm.trans (hBhat_tr i))
    simpa [Nat.cast_mul] using hre
   have hle_R : (Module.finrank ℂ (LinearMap.range (mulVecLin (T * cPr bdB i))) : ℝ) ≤
     min (Module.finrank ℂ (LinearMap.range (mulVecLin (cPr bdB i))) : ℝ)
      (Module.finrank ℂ (LinearMap.range (mulVecLin (πB (cPr bdB i)))) : ℝ) := by
    exact_mod_cast hle
   rwa [htr1, htr2] at hle_R
  exact (Nat.cast_le.mpr h1).trans (by rw [Nat.cast_sum]; exact sum_le_sum fun i _ => h2 i)
 obtain ⟨Pker, hPker_h, hPker_p, hT_Pker, hPker_tr⟩ := exists_ker_proj T
 have hker_le : ((Pker.trace).re : ℝ) ≤ 3 * ε ^ 2 * (d : ℝ) := by
  have hV_split : hsSq (V * Pker) = hsSq (Q * V * Pker) + hsSq ((1 - Q) * V * Pker) := by
   have hQ1 : Q * (1 - Q) = 0 := by rw [mms, mm1, hQp, sub_self]
   have h1 : V * Pker = Q * V * Pker + (1 - Q) * V * Pker := by
    rw [msm, m1m, msm]; abel
   have hC : ((hsSq (V * Pker) : ℝ) : ℂ) =
     ((hsSq (Q * V * Pker) : ℝ) : ℂ) + ((hsSq ((1 - Q) * V * Pker) : ℝ) : ℂ) := by
    rw [hsSq_trC, hsSq_trC, hsSq_trC]
    conv_lhs => rw [h1]
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
     trace_add, trace_add, trace_add]
    have horth : ((Q * V * Pker)ᴴ * ((1 - Q) * V * Pker)).trace = 0 := by
     calc
      ((Q * V * Pker)ᴴ * ((1 - Q) * V * Pker)).trace
       = (Pkerᴴ * Vᴴ * (Q * (1 - Q)) * V * Pker).trace := by
         simp only [ctM, hQh.eq, mma]
      _ = (0 : ℂ) := by rw [hQ1, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, trace_zero]
    have horth' : (((1 - Q) * V * Pker)ᴴ * (Q * V * Pker)).trace = 0 := by
     have hc := congrArg star horth
     rw [star_zero, ← trace_conjTranspose, ctM,
      ctct] at hc
     exact hc
    rw [horth, horth']; ring
   exact_mod_cast hC
  have htrP : ((Pker.trace).re : ℝ) = hsSq (V * Pker) := by
   rw [hsSq_isoL V (dilV_star_mul bdA) Pker, hsSq_tr, hPker_h.eq, hPker_p]
  have hterm1 : hsSq (Q * V * Pker) ≤ ε ^ 2 * (d : ℝ) := by
   have h1 : hsSq (Q * V * Pker) = hsSq ((ιQᴴ * V - T) * Pker) := by
    rw [msm, hT_Pker, sub_zero, ← hsSq_isoL ιQ hιQ_star,
     ← mma, ← mma, hιQ_mul]
   rw [h1, ← hsSq_ct, ctM, hPker_h.eq]
   calc
    hsSq (Pker * (ιQᴴ * V - T)ᴴ)
     ≤ hsSq ((ιQᴴ * V - T)ᴴ) := hsSq_proj_mul_le Pker hPker_h.eq hPker_p _
    _ = hsSq (T - ιQᴴ * V) := by rw [hsSq_ct, ← hsSq_neg, neg_sub]
    _ ≤ ε ^ 2 * (d : ℝ) := hT_diff
  have hterm2 : hsSq ((1 - Q) * V * Pker) ≤ 2 * ε ^ 2 * (d : ℝ) := by
   rw [← hsSq_ct, ctM, hPker_h.eq]
   calc
    hsSq (Pker * ((1 - Q) * V)ᴴ)
     ≤ hsSq (((1 - Q) * V)ᴴ) := hsSq_proj_mul_le Pker hPker_h.eq hPker_p _
    _ = hsSq ((1 - Q) * V) := hsSq_ct _
    _ ≤ 2 * ε ^ 2 * (d : ℝ) := hhs_1Q_V
  linarith
 have hrk_null : (Module.finrank ℂ (LinearMap.range (mulVecLin T)) : ℝ) +
   ((Pker.trace).re : ℝ) = (d : ℝ) := by
  rw [hPker_tr]
  have h := LinearMap.finrank_range_add_finrank_ker (mulVecLin T)
  rw [Module.finrank_fin_fun] at h
  exact_mod_cast h
 have hsum_d : ∑ i : Fin bdB.t, (bdB.r i : ℝ) * (bdB.s i : ℝ) = (d : ℝ) := by
  have h1 : ∑ i : Fin bdB.t, (cPr bdB i).trace = (d : ℂ) := by
   rw [← trace_sum, sum_cPr, trace_one, card_fin]
  have hterm : ∀ i : Fin bdB.t, (cPr bdB i).trace = ((bdB.r i * bdB.s i : ℕ) : ℂ) := by
   intro i; rw [← sum_matUnitA_diag bdB i, trace_sum]
   simp_rw [trace_matUnitA_diag]; simp [sum_const, nsmul_eq_mul, Nat.cast_mul]
  simp_rw [hterm] at h1
  have hre := congrArg Complex.re h1
  simpa [re_sum, Nat.cast_mul] using hre
 have hsum_m : ∑ i : Fin bdB.t, (bdB.r i : ℝ) * (q' i : ℝ) = (m : ℝ) := by
  have h1 : ∑ i : Fin bdB.t, (πB (cPr bdB i)).trace = (m : ℂ) := by
   have hsum_π : ∀ {α : Type} [DecidableEq α] (s : Finset α) (f : α → Matrix (Fin d) (Fin d) ℂ),
     πB (∑ a ∈ s, f a) = ∑ a ∈ s, πB (f a) := by
    intro α _ s f
    induction s using induction_on with
    | empty => have := hπB_smul 0 0; simpa using this
    | insert a s ha ih => rw [sum_insert ha, hπB_add, ih, sum_insert ha]
   rw [← trace_sum, ← hsum_π, sum_cPr, hπB_one, trace_one, card_fin]
  simp_rw [hBhat_tr] at h1
  have hre := congrArg Complex.re h1
  simpa [re_sum, Nat.cast_mul] using hre
 have habs_eq : ∑ i : Fin bdB.t, (bdB.r i : ℝ) * |(q' i : ℝ) - (bdB.s i : ℝ)| =
   (m : ℝ) + (d : ℝ) -
    2 * ∑ i : Fin bdB.t, min ((bdB.r i : ℝ) * (bdB.s i : ℝ)) ((bdB.r i : ℝ) * (q' i : ℝ)) := by
  have hterm : ∀ i : Fin bdB.t,
    (bdB.r i : ℝ) * |(q' i : ℝ) - (bdB.s i : ℝ)| =
     (bdB.r i : ℝ) * (q' i : ℝ) + (bdB.r i : ℝ) * (bdB.s i : ℝ) -
      2 * min ((bdB.r i : ℝ) * (bdB.s i : ℝ)) ((bdB.r i : ℝ) * (q' i : ℝ)) := by
   intro i
   have hr_nn : (0 : ℝ) ≤ (bdB.r i : ℝ) := Nat.cast_nonneg _
   by_cases hle : (bdB.s i : ℝ) ≤ (q' i : ℝ)
   ·
    have hle' := mul_le_mul_of_nonneg_left hle hr_nn
    rw [abs_of_nonneg (sub_nonneg.mpr hle), min_eq_left hle']; ring
   ·
    push Not at hle
    have hle' := mul_le_mul_of_nonneg_left (le_of_lt hle) hr_nn
    rw [abs_of_neg (sub_neg.mpr hle), min_eq_right hle']; ring
  simp_rw [hterm, sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
   hsum_m, hsum_d]
 have hm_le : (m : ℝ) - (d : ℝ) ≤ 2 * ε ^ 2 * (d : ℝ) := (le_abs_self _).trans hm_diff
 linarith
lemma exists_bratteliCorrection {d : ℕ}
  {B A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdB : BDec B) (bdA : BDec A)
  {ε : ℝ} (hε : 0 ≤ ε)
  (hinc : ∀ b ∈ B, ‖CLM b‖ ≤ 1 → hsSq (b - cExp A b) ≤ ε ^ 2 * (d : ℝ)) :
  Nonempty (BCData bdB bdA ε) := by
 classical
 obtain ⟨Q, hQh, hQp, hQ_comm_B, hQ_comm_A', hQ_tr_diff, hhs_1Q_V⟩ :=
  exists_dilation_cutoff bdB bdA hinc
 obtain ⟨m, ιQ, hιQ_star, hιQ_mul, hm_tr⟩ := exists_isometry_of_proj hQh hQp
 have hm_diff : |(m : ℝ) - (d : ℝ)| ≤ 2 * ε ^ 2 * (d : ℝ) := by rw [hm_tr]; exact hQ_tr_diff
 let πB (b : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin m) (Fin m) ℂ := ιQᴴ * dRB bdA b * ιQ
 let πA' (c : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin m) (Fin m) ℂ := ιQᴴ * dilRhoA' bdA c * ιQ
 have hπB_one : πB 1 = 1 := by simp [πB, dilRhoB_one, hιQ_star]
 have hπB_add : ∀ x y, πB (x + y) = πB x + πB y := fun x y => by
  simp [πB, dilRhoB_add, Matrix.mul_add, Matrix.add_mul]
 have hπB_smul : ∀ (α : ℂ) x, πB (α • x) = α • πB x := fun α x => by
  simp [πB, dilRhoB_smul, Matrix.mul_smul, Matrix.smul_mul]
 have hπB_star : ∀ x, πB xᴴ = (πB x)ᴴ := fun x => by
  simp [πB, dilRhoB_star, mma]
 have hπB_mul : ∀ x y, x ∈ B → y ∈ B → πB (x * y) = πB x * πB y := fun x y hx _ => by
  dsimp only [πB]
  have h1 : ιQᴴ * (ιQ * ιQᴴ) = ιQᴴ := by rw [← mma, hιQ_star, m1m]
  calc
   ιQᴴ * dRB bdA (x * y) * ιQ
    = (ιQᴴ * (ιQ * ιQᴴ)) * (dRB bdA x * dRB bdA y) * ιQ := by rw [dilRhoB_mul, h1]
   _ = ιQᴴ * (Q * dRB bdA x * dRB bdA y) * ιQ := by rw [hιQ_mul]; simp only [mma]
   _ = ιQᴴ * (dRB bdA x * Q * dRB bdA y) * ιQ := by rw [← hQ_comm_B x hx]
   _ = (ιQᴴ * dRB bdA x * ιQ) * (ιQᴴ * dRB bdA y * ιQ) := by rw [← hιQ_mul]; simp only [mma]
 have hπB_opNorm : ∀ x, ‖CLM (πB x)‖ ≤ ‖CLM x‖ := fun x => by
  have hP : (ιQᴴᴴ * ιQᴴ) * (ιQᴴᴴ * ιQᴴ) = ιQᴴᴴ * ιQᴴ := by
   rw [ctct, hιQ_mul, hQp]
  have h1 := opN_conjPI ιQᴴ hP (dRB bdA x)
  simp only [ctct] at h1
  exact h1.trans (dilRhoB_opNorm bdA x)
 have hπA'_one : πA' 1 = 1 := by simp [πA', dilRhoA'_one, hιQ_star]
 have hπA'_add : ∀ c₁ c₂, πA' (c₁ + c₂) = πA' c₁ + πA' c₂ := fun c₁ c₂ => by
  simp [πA', dilRhoA'_add, Matrix.mul_add, Matrix.add_mul]
 have hπA'_smul : ∀ (α : ℂ) c, πA' (α • c) = α • πA' c := fun α c => by
  simp [πA', dilRhoA'_smul, Matrix.mul_smul, Matrix.smul_mul]
 have hπA'_star : ∀ c, πA' cᴴ = (πA' c)ᴴ := fun c => by
  simp [πA', dilRhoA'_star, mma]
 have hπA'_mul : ∀ c₁ c₂, c₁ ∈ comm A → c₂ ∈ comm A → πA' (c₁ * c₂) = πA' c₁ * πA' c₂ :=
  fun c₁ c₂ hc₁ hc₂ => by
   dsimp only [πA']
   have h1 : ιQᴴ * (ιQ * ιQᴴ) = ιQᴴ := by rw [← mma, hιQ_star, m1m]
   calc
    ιQᴴ * dilRhoA' bdA (c₁ * c₂) * ιQ
     = (ιQᴴ * (ιQ * ιQᴴ)) * (dilRhoA' bdA c₁ * dilRhoA' bdA c₂) * ιQ := by
       rw [dilRhoA'_mul bdA hc₁ hc₂, h1]
    _ = ιQᴴ * (Q * dilRhoA' bdA c₁ * dilRhoA' bdA c₂) * ιQ := by rw [hιQ_mul]; simp only [mma]
    _ = ιQᴴ * (dilRhoA' bdA c₁ * Q * dilRhoA' bdA c₂) * ιQ := by rw [← hQ_comm_A' c₁ hc₁]
    _ = (ιQᴴ * dilRhoA' bdA c₁ * ιQ) * (ιQᴴ * dilRhoA' bdA c₂ * ιQ) := by rw [← hιQ_mul]; simp only [mma]
 have hπ_comm : ∀ b ∈ B, ∀ c ∈ comm A, πB b * πA' c = πA' c * πB b := fun b hb c hc => by
  dsimp only [πB, πA']
  calc
   (ιQᴴ * dRB bdA b * ιQ) * (ιQᴴ * dilRhoA' bdA c * ιQ)
    = ιQᴴ * (dRB bdA b * Q * dilRhoA' bdA c) * ιQ := by rw [← hιQ_mul]; simp only [mma]
   _ = ιQᴴ * (Q * (dRB bdA b * dilRhoA' bdA c)) * ιQ := by rw [hQ_comm_B b hb]; simp only [mma]
   _ = ιQᴴ * (Q * (dilRhoA' bdA c * dRB bdA b)) * ιQ := by rw [dilRho_comm]
   _ = ιQᴴ * (dilRhoA' bdA c * Q * dRB bdA b) * ιQ := by
      rw [← mma Q, ← hQ_comm_A' c hc]
   _ = (ιQᴴ * dilRhoA' bdA c * ιQ) * (ιQᴴ * dRB bdA b * ιQ) := by rw [← hιQ_mul]; simp only [mma]
 obtain ⟨Bhat, q', bdBhat, eB, hBhat_mem, hBhat_r, hBhat_s, hBhat_z, hBhat_tr, hBhat_zero, hBhat_lift⟩ :=
  blockDecomp_of_hom_A bdB πB hπB_one hπB_add hπB_smul hπB_mul hπB_star
 obtain ⟨Ahat, r', bdAhat, eA, hAhat_mem, hAhat_r, hAhat_s, hAhat_z, hAhat_tr, hAhat_zero⟩ :=
  blockDecomp_of_hom_C bdA πA' hπA'_one (fun c₁ c₂ _ _ => hπA'_add c₁ c₂)
   (fun α c _ => hπA'_smul α c) hπA'_mul (fun c _ => hπA'_star c)
 have hBAhat : Bhat ≤ Ahat := by
  intro bhat hbhat
  obtain ⟨b, hb, rfl⟩ := (hBhat_mem bhat).mp hbhat
  exact (hAhat_mem _).mpr fun c hc => hπ_comm b hb c hc
 obtain ⟨W, hW_src, hW_tgt, hW_src_tr, hW_tgt_tr, hW_comm_A', hW_comm_AB, hW_approx_B⟩ :=
  exists_bratteli_polar bdA hε hinc hQh hQp hQ_comm_B hQ_comm_A' hhs_1Q_V hιQ_star hιQ_mul hm_diff
 change ∀ c ∈ comm A, πA' c * W = W * c at hW_comm_A'
 change ∀ x ∈ A, x ∈ B → πB x * W = W * x at hW_comm_AB
 change ∀ b ∈ B, ‖CLM b‖ ≤ 1 → hsN (πB b * W - W * b) ≤ 6 * ε * sqrt (d : ℝ) at hW_approx_B
 have hWch_eq : ∀ c ∈ comm A, Wᴴ * πA' c = c * Wᴴ := by
  intro c hc
  have hc' : cᴴ ∈ comm A := star_mem hc
  have h1 := congrArg Matrix.conjTranspose (hW_comm_A' cᴴ hc')
  rw [ctM (πA' cᴴ) W, ctM W cᴴ, ← hπA'_star,
   ctct] at h1
  exact h1
 have hW_conj_A : ∀ a ∈ A, W * a * Wᴴ ∈ Ahat := by
  intro a ha
  rw [hAhat_mem]; intro c hc
  calc
   (W * a * Wᴴ) * πA' c = W * a * (Wᴴ * πA' c) := by simp only [mma]
   _ = W * (a * c) * Wᴴ := by rw [hWch_eq c hc]; simp only [mma]
   _ = W * (c * a) * Wᴴ := by rw [hc a ha]
   _ = (W * c) * (a * Wᴴ) := by simp only [mma]
   _ = πA' c * (W * a * Wᴴ) := by rw [← hW_comm_A' c hc]; simp only [mma]
 have hW_conj_Ahat : ∀ ahat ∈ Ahat, Wᴴ * ahat * W ∈ A := by
  intro ahat hahat
  rw [← bicommutant_eq A, mem_commutant]; intro c hc
  have hcomm := (hAhat_mem ahat).mp hahat c hc
  calc
   (Wᴴ * ahat * W) * c = Wᴴ * ahat * (W * c) := by simp only [mma]
   _ = Wᴴ * (ahat * πA' c) * W := by rw [← hW_comm_A' c hc]; simp only [mma]
   _ = (Wᴴ * πA' c) * ahat * W := by rw [hcomm]; simp only [mma]
   _ = c * (Wᴴ * ahat * W) := by rw [hWch_eq c hc]; simp only [mma]
 have hA_mult : ∑ j : Fin bdA.t, (bdA.s j : ℝ) * |(r' j : ℝ) - (bdA.r j : ℝ)| ≤ 6 * ε ^ 2 * (d : ℝ) :=
  bratteli_A_mult bdA πA' r' W hπA'_one hπA'_add hπA'_smul hπA'_mul hπA'_star hAhat_tr
   hW_src hW_src_tr hW_comm_A' hm_diff
 have hB_mult : ∑ i : Fin bdB.t, (bdB.r i : ℝ) * |(q' i : ℝ) - (bdB.s i : ℝ)| ≤ 8 * ε ^ 2 * (d : ℝ) :=
  bratteli_B_mult bdB bdA hinc hQh hQp hQ_comm_B hhs_1Q_V hιQ_star hιQ_mul hm_diff
   πB (fun _ => rfl) hπB_one hπB_add hπB_smul hπB_mul hπB_star q' hBhat_tr
 exact ⟨{
  m := m, Bhat := Bhat, Ahat := Ahat, hBAhat := hBAhat, q' := q', r' := r',
  bdBhat := bdBhat, bdAhat := bdAhat, eB := eB, eA := eA, πB := πB, πA' := πA', W := W,
  hm_diff := hm_diff, hB_mult := hB_mult, hA_mult := hA_mult,
  hBhat_mem := hBhat_mem, hBhat_r := hBhat_r, hBhat_s := hBhat_s, hBhat_z := hBhat_z,
  hBhat_tr := hBhat_tr, hBhat_zero := hBhat_zero, hBhat_lift := hBhat_lift,
  hAhat_mem := hAhat_mem, hAhat_r := hAhat_r, hAhat_s := hAhat_s, hAhat_z := hAhat_z,
  hAhat_tr := hAhat_tr, hAhat_zero := hAhat_zero,
  hπB_one := hπB_one, hπB_add := hπB_add, hπB_smul := hπB_smul, hπB_mul := hπB_mul,
  hπB_star := hπB_star, hπB_opNorm := hπB_opNorm,
  hπA'_one := hπA'_one, hπA'_add := hπA'_add, hπA'_smul := hπA'_smul, hπA'_mul := hπA'_mul,
  hπA'_star := hπA'_star, hπ_comm := hπ_comm,
  hW_src := hW_src, hW_tgt := hW_tgt, hW_src_tr := hW_src_tr, hW_tgt_tr := hW_tgt_tr,
  hW_comm_A' := hW_comm_A', hW_comm_AB := hW_comm_AB, hW_approx_B := hW_approx_B,
  hW_conj_A := hW_conj_A, hW_conj_Ahat := hW_conj_Ahat }⟩
end BratteliCorrection
/- ### 8. No-drift theorem, coherent models, and main theorem -/
section NoDrift
def bFn (t lam : ℝ) : ℝ := lam / (lam + t)
lemma betaFn_pos {t lam : ℝ} (ht : 0 < t) (hl : 0 < lam) : 0 < bFn t lam :=
 div_pos hl (by linarith)
lemma betaFn_lt_one {t lam : ℝ} (ht : 0 < t) (hl : 0 < lam) : bFn t lam < 1 := by
 dsimp only [bFn]
 rw [div_lt_one (by linarith)]
 linarith
lemma betaFn_mono {t lam₁ lam₂ : ℝ} (ht : 0 < t) (hl₁ : 0 < lam₁) (hle : lam₁ ≤ lam₂) :
  bFn t lam₁ ≤ bFn t lam₂ := by
 dsimp only [bFn]
 have h1 : 0 < lam₁ + t := by linarith
 have h2 : 0 < lam₂ + t := by linarith
 rw [div_le_div_iff₀ h1 h2]
 nlinarith
lemma abs_betaFn_sub_s_le {t r s q' : ℝ}
  (ht : 0 < t) (hr : 0 < r) (hs : 0 < s) (hq : 0 < q') :
  |bFn t (r / s) - bFn t (r / q')| ≤ |q' - s| / q' := by
 dsimp only [bFn]
 have h1 : 0 < r / s + t := by positivity
 have h2 : 0 < r / q' + t := by positivity
 have h3 : 0 < r + t * s := by positivity
 have h4 : 0 < r + t * q' := by positivity
 have heq : r / s / (r / s + t) - r / q' / (r / q' + t) =
   r * t * (q' - s) / ((r + t * s) * (r + t * q')) := by
  field_simp [ne_of_gt hs, ne_of_gt hq, ne_of_gt h1, ne_of_gt h2, ne_of_gt h3, ne_of_gt h4]
  ring
 rw [heq, abs_div, abs_mul, abs_of_pos (mul_pos hr ht), abs_of_pos (mul_pos h3 h4)]
 rw [div_le_div_iff₀ (mul_pos h3 h4) hq]
 have hprod : r * t * q' ≤ (r + t * s) * (r + t * q') := by
  have : 0 ≤ r * r + t * s * r + t * s * (t * q') := by positivity
  linarith
 have habs : 0 ≤ |q' - s| := abs_nonneg _
 nlinarith
lemma abs_betaFn_sub_r_le {t r r' s : ℝ}
  (ht : 0 < t) (hr : 0 < r) (hr' : 0 < r') (hs : 0 < s) :
  |bFn t (r / s) - bFn t (r' / s)| ≤ |r' - r| / r' := by
 dsimp only [bFn]
 have h1 : 0 < r / s + t := by positivity
 have h2 : 0 < r' / s + t := by positivity
 have h3 : 0 < r + t * s := by positivity
 have h4 : 0 < r' + t * s := by positivity
 have heq : r / s / (r / s + t) - r' / s / (r' / s + t) =
   t * s * (r - r') / ((r + t * s) * (r' + t * s)) := by
  field_simp [ne_of_gt hs, ne_of_gt h1, ne_of_gt h2, ne_of_gt h3, ne_of_gt h4]
  ring
 rw [heq, abs_div, abs_mul, abs_of_pos (mul_pos ht hs), abs_of_pos (mul_pos h3 h4),
  abs_sub_comm r r']
 rw [div_le_div_iff₀ (mul_pos h3 h4) hr']
 have hprod : t * s * r' ≤ (r + t * s) * (r' + t * s) := by
  have : 0 ≤ r * r' + r * (t * s) + (t * s) * (t * s) := by positivity
  linarith
 have habs : 0 ≤ |r' - r| := abs_nonneg _
 nlinarith
lemma betaFn_ratio_eq {t lam₁ lam₂ : ℝ} (ht : 0 < t) (hl₁ : 0 < lam₁) (hl₂ : 0 < lam₂) :
  (bFn t lam₁ * (1 - bFn t lam₂)) / (bFn t lam₂ * (1 - bFn t lam₁)) = lam₁ / lam₂ := by
 dsimp only [bFn]
 have h1 : lam₁ + t ≠ 0 := ne_of_gt (by linarith)
 have h2 : lam₂ + t ≠ 0 := ne_of_gt (by linarith)
 have ht0 : t ≠ 0 := ne_of_gt ht
 have hl20 : lam₂ ≠ 0 := ne_of_gt hl₂
 field_simp [h1, h2, ht0, hl20]; ring
lemma ratio_defect_le_abs {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
  1 - (a * (1 - b)) / (b * (1 - a)) ≤ 16 * (|a - 1 / 2| + |b - 1 / 2|) := by
 have hb_pos : 0 < b := lt_of_lt_of_le ha hab
 have h1a_pos : 0 < 1 - a := by linarith
 have h1b_pos : 0 < 1 - b := by linarith
 have hden_pos : 0 < b * (1 - a) := mul_pos hb_pos h1a_pos
 have hnum_pos : 0 < a * (1 - b) := mul_pos ha h1b_pos
 by_cases hfar : (1 / 4 : ℝ) ≤ |a - 1 / 2| ∨ (1 / 4 : ℝ) ≤ |b - 1 / 2|
 ·
  have hq : 0 < (a * (1 - b)) / (b * (1 - a)) := div_pos hnum_pos hden_pos
  rcases hfar with hfar | hfar <;> linarith [abs_nonneg (a - 1 / 2), abs_nonneg (b - 1 / 2)]
 ·
  push Not at hfar
  rcases hfar with ⟨ha_cl, hb_cl⟩
  rw [abs_lt] at ha_cl hb_cl
  have hden_ge : (1 / 16 : ℝ) ≤ b * (1 - a) := by nlinarith
  have heq : 1 - (a * (1 - b)) / (b * (1 - a)) = (b - a) / (b * (1 - a)) := by
   field_simp [ne_of_gt hden_pos]; ring
  rw [heq, div_le_iff₀ hden_pos]
  have hba_nn : 0 ≤ b - a := by linarith
  have hba_le : b - a ≤ |a - 1 / 2| + |b - 1 / 2| := by
   have h1 : -(a - 1 / 2) ≤ |a - 1 / 2| := neg_le_abs _
   have h2 : b - 1 / 2 ≤ |b - 1 / 2| := le_abs_self _
   linarith
  nlinarith
lemma orthProj_tr_nn {m : ℕ} {P : Matrix (Fin m) (Fin m) ℂ}
  (hPh : Pᴴ = P) (hPp : P * P = P) : 0 ≤ (P.trace).re := by
 have h : hsSq P = (P.trace).re := by rw [hsSq_tr, hPh, hPp]
 rw [← h]; exact hsSq_nonneg P
lemma orthog_proj_family_hsSq {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
  (P : α → Matrix (Fin m) (Fin m) ℂ)
  (hPh : ∀ a, (P a)ᴴ = P a)
  (hPmul : ∀ a b, P a * P b = if a = b then P a else 0)
  (c : α → ℝ) :
  hsSq (∑ a : α, (c a : ℂ) • P a) = ∑ a : α, (c a) ^ 2 * ((P a).trace).re := by
 rw [hsSq_tr, conjTranspose_sum, Matrix.sum_mul, trace_sum, re_sum]
 refine sum_congr rfl fun a _ => ?_
 rw [Matrix.mul_sum, trace_sum, re_sum, sum_eq_single a]
 ·
  rw [conjTranspose_smul, hPh a, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
   hPmul a a, if_pos rfl, trace_smul, smul_eq_mul]
  rw [star_def, conj_ofReal, ← pow_two, ← Complex.ofReal_pow,
   Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
 ·
  intro b _ hba
  rw [conjTranspose_smul, hPh a, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
   hPmul a b, if_neg hba.symm, smul_zero, trace_zero, zero_re]
 · intro h; exact absurd (mem_univ a) h
lemma orthog_proj_family_trace_re {α : Type*} [Fintype α] {m : ℕ}
  (P : α → Matrix (Fin m) (Fin m) ℂ) (c : α → ℝ) :
  ((∑ a : α, (c a : ℂ) • P a).trace).re = ∑ a : α, c a * ((P a).trace).re := by
 rw [trace_sum, re_sum]
 refine sum_congr rfl fun a _ => ?_
 rw [trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
  zero_mul, sub_zero]
lemma orthog_proj_family_opNorm_le {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
  (P : α → Matrix (Fin m) (Fin m) ℂ)
  (hPh : ∀ a, (P a)ᴴ = P a)
  (hPmul : ∀ a b, P a * P b = if a = b then P a else 0)
  (hPsum : ∑ a : α, P a = 1)
  (c : α → ℝ) {M : ℝ} (hM : 0 ≤ M) (hc : ∀ a, |c a| ≤ M) :
  ‖CLM (∑ a : α, (c a : ℂ) • P a)‖ ≤ M := by
 refine ContinuousLinearMap.opNorm_le_bound _ hM fun v => ?_
 have horth : ∀ (a b : α), a ≠ b → ⟪CLM (P a) v, CLM (P b) v⟫_ℂ = 0 := by
  intro a b hab
  have hadj : ContinuousLinearMap.adjoint (CLM (P a)) = CLM (P a) := by
   rw [toCLM_adjoint, hPh a]
  calc
   ⟪CLM (P a) v, CLM (P b) v⟫_ℂ
    = ⟪v, ContinuousLinearMap.adjoint (CLM (P a)) (CLM (P b) v)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
   _ = ⟪v, CLM (P a * P b) v⟫_ℂ := by
      rw [hadj]; dsimp only [CLM]; rw [map_mul]; rfl
   _ = 0 := by dsimp only [CLM]; rw [hPmul a b, if_neg hab, map_zero]; simp
 have hpyth : ∀ f : α → ℂ,
   ‖∑ a : α, f a • CLM (P a) v‖ ^ 2 = ∑ a : α, ‖f a‖ ^ 2 * ‖CLM (P a) v‖ ^ 2 := by
  intro f
  have hC : ((‖∑ a : α, f a • CLM (P a) v‖ ^ 2 : ℝ) : ℂ) =
    ((∑ a : α, ‖f a‖ ^ 2 * ‖CLM (P a) v‖ ^ 2 : ℝ) : ℂ) := by
   have hself : ((‖∑ a : α, f a • CLM (P a) v‖ ^ 2 : ℝ) : ℂ) =
     ⟪∑ a : α, f a • CLM (P a) v, ∑ a : α, f a • CLM (P a) v⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]; simp
   rw [hself, sum_inner, Complex.ofReal_sum]
   refine sum_congr rfl fun a _ => ?_
   rw [inner_sum, sum_eq_single a]
   ·
    rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
    have hmul : (starRingEnd ℂ) (f a) * f a = ((‖f a‖ ^ 2 : ℝ) : ℂ) := by
     rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← mul_assoc, hmul, ofReal_mul]; simp
   ·
    intro b _ hba
    rw [inner_smul_left, inner_smul_right, horth a b hba.symm, mul_zero, mul_zero]
   · intro h; exact absurd (mem_univ a) h
  exact Complex.ofReal_injective hC
 have hv_sum : v = ∑ a : α, (1 : ℂ) • CLM (P a) v := by
  have h1 : CLM (∑ a : α, P a) v = v := by rw [hPsum]; simp [CLM]
  conv_lhs => rw [← h1]
  dsimp only [CLM]
  rw [map_sum, FunLike.coe_sum, Finset.sum_apply]
  refine sum_congr rfl fun a _ => by simp
 have hv_sq : ‖v‖ ^ 2 = ∑ a : α, ‖CLM (P a) v‖ ^ 2 := by
  conv_lhs => rw [hv_sum]
  rw [hpyth]; simp
 have hXv : CLM (∑ a : α, (c a : ℂ) • P a) v = ∑ a : α, (c a : ℂ) • CLM (P a) v := by
  dsimp only [CLM]
  rw [map_sum, FunLike.coe_sum, Finset.sum_apply]
  refine sum_congr rfl fun a _ => by rw [map_smul]; rfl
 have hsq : ‖CLM (∑ a : α, (c a : ℂ) • P a) v‖ ^ 2 ≤ (M * ‖v‖) ^ 2 := by
  rw [hXv, hpyth, mul_pow, hv_sq, Finset.mul_sum]
  refine sum_le_sum fun a _ => ?_
  rw [norm_real, Real.norm_eq_abs]
  have hca : |c a| ^ 2 ≤ M ^ 2 := by nlinarith [hc a, abs_nonneg (c a)]
  exact mul_le_mul_of_nonneg_right hca (sq_nonneg _)
 have hrt := sqrt_le_sqrt hsq
 rwa [sqrt_sq (norm_nonneg _), sqrt_sq (mul_nonneg hM (norm_nonneg _))] at hrt
lemma weighted_cs {α : Type*} [Fintype α] (a w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
  ∑ x : α, |a x| * w x ≤ sqrt (∑ x : α, a x ^ 2 * w x) * sqrt (∑ x : α, w x) := by
 have h1 := Finset.sum_mul_sq_le_sq_mul_sq univ
  (fun x => |a x| * sqrt (w x)) (fun x => sqrt (w x))
 have hL : ∑ x : α, |a x| * sqrt (w x) * sqrt (w x) = ∑ x : α, |a x| * w x :=
  sum_congr rfl fun x _ => by rw [mul_assoc, mul_self_sqrt (hw x)]
 have hR1 : ∑ x : α, (|a x| * sqrt (w x)) ^ 2 = ∑ x : α, a x ^ 2 * w x :=
  sum_congr rfl fun x _ => by rw [mul_pow, sq_abs, sq_sqrt (hw x)]
 have hR2 : ∑ x : α, sqrt (w x) ^ 2 = ∑ x : α, w x :=
  sum_congr rfl fun x _ => sq_sqrt (hw x)
 rw [hL, hR1, hR2] at h1
 have hrt := sqrt_le_sqrt h1
 rw [sqrt_sq (sum_nonneg fun x _ => mul_nonneg (abs_nonneg _) (hw x)),
  sqrt_mul (sum_nonneg fun x _ => mul_nonneg (sq_nonneg _) (hw x))] at hrt
 exact hrt
lemma norm_trace_mul_proj_le {m : ℕ} (X P : Matrix (Fin m) (Fin m) ℂ)
  (hPh : Pᴴ = P) (hPp : P * P = P) :
  ‖(X * P).trace‖ ≤ ‖CLM X‖ * ((P.trace).re) := by
 have heq : (X * P).trace = (Pᴴ * (X * P)).trace := by
  calc
   (X * P).trace = (X * (P * P)).trace := by rw [hPp]
   _ = ((X * P) * P).trace := by rw [mma]
   _ = (P * (X * P)).trace := trace_mul_comm _ _
   _ = (Pᴴ * (X * P)).trace := by rw [hPh]
 rw [heq]
 have hPsq : hsSq P = (P.trace).re := by rw [hsSq_tr, hPh, hPp]
 calc
  ‖(Pᴴ * (X * P)).trace‖ ≤ hsN P * hsN (X * P) := norm_trace_conjTranspose_mul_le P (X * P)
  _ ≤ hsN P * (‖CLM X‖ * hsN P) :=
    mul_le_mul_of_nonneg_left (hsN_mulL X P) (hsN_nn P)
  _ = ‖CLM X‖ * hsN P ^ 2 := by ring
  _ = ‖CLM X‖ * ((P.trace).re) := by rw [hsNorm_sq, hPsq]
lemma norm_trace_proj_mul_le {m : ℕ} (P X : Matrix (Fin m) (Fin m) ℂ)
  (hPh : Pᴴ = P) (hPp : P * P = P) :
  ‖(P * X).trace‖ ≤ ‖CLM X‖ * ((P.trace).re) := by
 rw [trace_mul_comm]
 exact norm_trace_mul_proj_le X P hPh hPp
def conjAlg {d : ℕ}
  (u : Matrix (Fin d) (Fin d) ℂ) (hu : u ∈ unitaryGroup (Fin d) ℂ)
  (A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)) :
  StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ) where
 carrier := {X | u * X * uᴴ ∈ A}
 mul_mem' {X Y} hX hY := by
  show u * (X * Y) * uᴴ ∈ A
  have hmul : u * (X * Y) * uᴴ = (u * X * uᴴ) * (u * Y * uᴴ) := by
   have hUs : uᴴ * u = 1 := star_mul_self_of_mem hu
   calc
    u * (X * Y) * uᴴ = u * X * (uᴴ * u) * Y * uᴴ := by
       rw [hUs, mm1]; simp only [mma]
    _ = (u * X * uᴴ) * (u * Y * uᴴ) := by simp only [mma]
  rw [hmul]; exact A.mul_mem hX hY
 one_mem' := by
  show u * 1 * uᴴ ∈ A
  rw [mm1, ← star_eq_conjTranspose, mul_star_self_of_mem hu]
  exact A.one_mem
 add_mem' {X Y} hX hY := by
  show u * (X + Y) * uᴴ ∈ A
  rw [Matrix.mul_add, Matrix.add_mul]; exact A.add_mem hX hY
 zero_mem' := by
  show u * 0 * uᴴ ∈ A
  rw [Matrix.mul_zero, Matrix.zero_mul]; exact A.zero_mem
 algebraMap_mem' r := by
  show u * algebraMap ℂ _ r * uᴴ ∈ A
  rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, mm1,
   ← star_eq_conjTranspose, mul_star_self_of_mem hu]
  exact A.smul_mem A.one_mem r
 star_mem' {X} hX := by
  show u * Xᴴ * uᴴ ∈ A
  have hst : u * Xᴴ * uᴴ = (u * X * uᴴ)ᴴ := by
   simp only [ctM, ctct, mma]
  rw [hst]; exact star_mem hX
lemma mem_conjStarSubalgebra {d : ℕ}
  {u : Matrix (Fin d) (Fin d) ℂ} (hu : u ∈ unitaryGroup (Fin d) ℂ)
  {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} {X : Matrix (Fin d) (Fin d) ℂ} :
  X ∈ conjAlg u hu A ↔ u * X * uᴴ ∈ A := Iff.rfl
def conjBD {d : ℕ}
  {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} (bdA : BDec A)
  (u : Matrix (Fin d) (Fin d) ℂ) (hu : u ∈ unitaryGroup (Fin d) ℂ) :
  BDec (conjAlg u hu A) where
 t := bdA.t
 r := bdA.r
 s := bdA.s
 hr := bdA.hr
 hs := bdA.hs
 U := uᴴ * bdA.U
 U_star_mul := by
  have hUm : u * uᴴ = 1 := mul_star_self_of_mem hu
  calc
   (uᴴ * bdA.U)ᴴ * (uᴴ * bdA.U) = bdA.Uᴴ * (u * uᴴ) * bdA.U := by
      simp only [ctM, ctct, mma]
   _ = 1 := by rw [hUm, mm1, bdA.U_star_mul]
 U_mul_star := by
  have hUs : uᴴ * u = 1 := star_mul_self_of_mem hu
  calc
   (uᴴ * bdA.U) * (uᴴ * bdA.U)ᴴ = uᴴ * (bdA.U * bdA.Uᴴ) * u := by
      simp only [ctM, ctct, mma]
   _ = 1 := by rw [bdA.U_mul_star, mm1, hUs]
 mem_iff X := by
  rw [mem_conjStarSubalgebra, bdA.mem_iff]
  refine exists_congr fun M => ?_
  have heq : (uᴴ * bdA.U)ᴴ * X * (uᴴ * bdA.U) = bdA.Uᴴ * (u * X * uᴴ) * bdA.U := by
   simp only [ctM, ctct, mma]
  rw [heq]
lemma cPr_conjBD {d : ℕ}
  {A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} (bdA : BDec A)
  (u : Matrix (Fin d) (Fin d) ℂ) (hu : u ∈ unitaryGroup (Fin d) ℂ) (i : Fin bdA.t) :
  cPr (conjBD bdA u hu) i = uᴴ * cPr bdA i * u := by
 dsimp only [cPr, conjBD]
 simp only [ctM, ctct, mma]
lemma condExp_centralProj_mul_eq {d : ℕ}
  {D A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} (hDA : D ≤ A)
  (bdD : BDec D) (bdA : BDec A) (j : Fin bdA.t) (k : Fin bdD.t) :
  cExp D (cPr bdA j * cPr bdD k) =
   ((((cPr bdA j * cPr bdD k).trace).re /
    ((bdD.r k * bdD.s k : ℕ) : ℝ)) : ℂ) • cPr bdD k := by
 let z := cPr bdA j
 let e := cPr bdD k
 let c := z * e
 have hzD' : z ∈ comm D := commutant_antitone hDA (cPr_comm bdA j)
 have heD' : e ∈ comm D := cPr_comm bdD k
 have hcD' : c ∈ comm D := (comm D).mul_mem hzD' heD'
 have hch : cᴴ = c := by
  dsimp only [c]
  rw [ctM, cPr_herm, cPr_herm, hzD' e (cPr_mem bdD k)]
 have hcp : c * c = c := by
  dsimp only [c]
  calc
   (z * e) * (z * e) = z * (e * z) * e := by simp only [mma]
   _ = (z * z) * (e * e) := by rw [← hzD' e (cPr_mem bdD k)]; simp only [mma]
   _ = z * e := by rw [cPr_mul, cPr_mul, if_pos rfl, if_pos rfl]
 have hc_tr_real : ((c.trace.re : ℝ) : ℂ) = c.trace := by
  have h1 : hsSq c = c.trace.re := by rw [hsSq_tr, hch, hcp]
  have h2 : ((hsSq c : ℝ) : ℂ) = c.trace := by rw [hsSq_trC, hch, hcp]
  rw [← h1, h2]
 let α : ℂ := ((c.trace.re / ((bdD.r k * bdD.s k : ℕ) : ℝ)) : ℂ)
 refine condExp_eq_of_mem_of_orthog D (D.smul_mem (cPr_mem bdD k) α) ?_
 intro y hy
 suffices h : (yᴴ * (c - α • e)).trace = 0 by
  have hc := congrArg star h
  rw [star_zero, ← trace_conjTranspose, ctM,
   ctct] at hc
  exact hc
 obtain ⟨M, _, hy_exp⟩ := expand_in_matUnitA bdD hy
 rw [hy_exp, conjTranspose_sum, Matrix.sum_mul, trace_sum]
 refine sum_eq_zero fun k' _ => ?_
 rw [conjTranspose_sum, Matrix.sum_mul, trace_sum]
 refine sum_eq_zero fun a _ => ?_
 rw [conjTranspose_sum, Matrix.sum_mul, trace_sum]
 refine sum_eq_zero fun b _ => ?_
 rw [conjTranspose_smul, Matrix.smul_mul, trace_smul, smul_eq_mul]
 suffices h0 : ((mUA bdD k' a b)ᴴ * (c - α • e)).trace = 0 by rw [h0, mul_zero]
 rw [matUnitA_conjTranspose, mms, Matrix.mul_smul, trace_sub, trace_smul,
  smul_eq_mul, sub_eq_zero]
 have hunit_e : ∀ (k₁ : Fin bdD.t) (p q : Fin (bdD.r k₁)),
   mUA bdD k₁ p q * cPr bdD k = if k₁ = k then mUA bdD k₁ p q else 0 := by
  intro k₁ p q
  rw [← sum_matUnitA_diag bdD k, Matrix.mul_sum]
  by_cases hk : k₁ = k
  ·
   subst hk
   rw [if_pos rfl, sum_eq_single q]
   · rw [mUA_mul, if_pos rfl]
   · intro r _ hrq; rw [mUA_mul, if_neg hrq.symm]
   · intro h; exact absurd (mem_univ q) h
  ·
   rw [if_neg hk]
   exact sum_eq_zero fun r _ => matUnitA_mul_ne bdD hk p q r r
 by_cases hk : k' = k
 ·
  subst hk
  by_cases hab : a = b
  ·
   subst hab
   have hcomm_eq : ∀ a' : Fin (bdD.r k'),
     (mUA bdD k' a' a' * c).trace = (mUA bdD k' a a * c).trace := by
    intro a'
    have h1 : mUA bdD k' a' a' = mUA bdD k' a' a * mUA bdD k' a a' := by
     rw [mUA_mul, if_pos rfl]
    have h2 : mUA bdD k' a a = mUA bdD k' a a' * mUA bdD k' a' a := by
     rw [mUA_mul, if_pos rfl]
    calc
     (mUA bdD k' a' a' * c).trace
      = (mUA bdD k' a' a * (mUA bdD k' a a' * c)).trace := by rw [h1, mma]
     _ = ((mUA bdD k' a a' * c) * mUA bdD k' a' a).trace := trace_mul_comm _ _
     _ = (mUA bdD k' a a' * (mUA bdD k' a' a * c)).trace := by
        rw [mma, hcD' _ (mUA_mem bdD k' a' a)]
     _ = (mUA bdD k' a a * c).trace := by rw [← mma, ← h2]
   have hsum_r : (bdD.r k' : ℂ) * (mUA bdD k' a a * c).trace = c.trace := by
    have h1 : (e * c).trace = c.trace := by
     dsimp only [c]
     rw [← mma, ← hzD' e (cPr_mem bdD k'), mma]
     dsimp only [e]; rw [cPr_mul, if_pos rfl]
    rw [← h1]; dsimp only [e]
    rw [← sum_matUnitA_diag bdD k', Matrix.sum_mul, trace_sum]
    simp_rw [hcomm_eq, sum_const, card_univ, card_fin, nsmul_eq_mul]
   rw [hunit_e k' a a, if_pos rfl, trace_matUnitA_diag]
   have hr0 : (bdD.r k' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (bdD.hr k'))
   have hs0 : (bdD.s k' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (bdD.hs k'))
   have hα_eq : α = c.trace / ((bdD.r k' : ℂ) * (bdD.s k' : ℂ)) := by
    dsimp only [α]
    rw [hc_tr_real, Nat.cast_mul, ofReal_mul,
     Complex.ofReal_natCast, Complex.ofReal_natCast]
   rw [hα_eq]
   apply mul_left_cancel₀ hr0
   rw [hsum_r]
   field_simp [hr0, hs0]
  ·
   have htr_comm : ∀ Y ∈ comm D, (mUA bdD k' b a * Y).trace = 0 := by
    intro Y hY
    have h1 : mUA bdD k' b a = mUA bdD k' b b * mUA bdD k' b a := by
     rw [mUA_mul, if_pos rfl]
    have h2 : mUA bdD k' b a * mUA bdD k' b b = 0 := by
     rw [mUA_mul, if_neg hab]
    calc
     (mUA bdD k' b a * Y).trace
      = (mUA bdD k' b b * (mUA bdD k' b a * Y)).trace := by
        conv_lhs => rw [h1]
        rw [mma]
     _ = ((mUA bdD k' b a * Y) * mUA bdD k' b b).trace := trace_mul_comm _ _
     _ = ((mUA bdD k' b a * mUA bdD k' b b) * Y).trace := by
        rw [mma, hY _ (mUA_mem bdD k' b b), ← mma]
     _ = 0 := by rw [h2, Matrix.zero_mul, trace_zero]
   rw [htr_comm c hcD', htr_comm e heD', mul_zero]
 ·
  have h1 : mUA bdD k' b a * c = 0 := by
   dsimp only [c]
   rw [hzD' e (cPr_mem bdD k), ← mma, hunit_e k' b a, if_neg hk,
    Matrix.zero_mul]
  rw [h1, hunit_e k' b a, if_neg hk, trace_zero, mul_zero]
lemma exists_cond_median {d : ℕ}
  {D A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} (hDA : D ≤ A)
  (bdD : BDec D) (bdA : BDec A) :
  ∃ (mu : Fin bdD.t → ℝ), (∀ k, 0 < mu k) ∧
   let x := ∑ j : Fin bdA.t, ∑ k : Fin bdD.t,
    (bFn (mu k) ((bdA.r j : ℝ) / (bdA.s j : ℝ)) : ℂ) •
     (cPr bdA j * cPr bdD k)
   x ∈ A ∧ ‖CLM x‖ ≤ 1 ∧ cExp D x = ((1 / 2 : ℝ) : ℂ) • 1 := by
 classical
 have hcomm : ∀ j k, cPr bdA j * cPr bdD k = cPr bdD k * cPr bdA j :=
  fun j k => commutant_antitone hDA (cPr_comm bdA j) _ (cPr_mem bdD k)
 have hmu_ex : ∀ k : Fin bdD.t, ∃ t : ℝ, 0 < t ∧
   ((bdD.r k * bdD.s k : ℕ) : ℝ)⁻¹ *
    ∑ j : Fin bdA.t,
     bFn t ((bdA.r j : ℝ) / (bdA.s j : ℝ)) *
      ((cPr bdA j * cPr bdD k).trace).re = 1 / 2 := by
  intro k
  let W : ℝ := ((bdD.r k * bdD.s k : ℕ) : ℝ)
  have hW_pos : 0 < W := by
   dsimp only [W]; exact Nat.cast_pos.mpr (Nat.mul_pos (bdD.hr k) (bdD.hs k))
  let w : Fin bdA.t → ℝ := fun j => ((cPr bdA j * cPr bdD k).trace).re
  have hw_nn : ∀ j, 0 ≤ w j := fun j => by
   dsimp only [w]
   refine orthProj_tr_nn ?_ ?_
   · rw [ctM, cPr_herm, cPr_herm, hcomm]
   ·
    calc
     (cPr bdA j * cPr bdD k) * (cPr bdA j * cPr bdD k)
      = (cPr bdA j * cPr bdA j) * (cPr bdD k * cPr bdD k) := by
        rw [mma, ← mma (cPr bdD k), ← hcomm,
         mma, mma]
     _ = cPr bdA j * cPr bdD k := by
        rw [cPr_mul, cPr_mul, if_pos rfl, if_pos rfl]
  have hw_sum : ∑ j : Fin bdA.t, w j = W := by
   dsimp only [w, W]
   rw [← re_sum, ← trace_sum, ← Matrix.sum_mul, sum_cPr, m1m]
   have ht : (cPr bdD k).trace = ((bdD.r k * bdD.s k : ℕ) : ℂ) := by
    rw [← sum_matUnitA_diag bdD k, trace_sum]
    simp_rw [trace_matUnitA_diag]; simp [sum_const, nsmul_eq_mul, Nat.cast_mul]
   rw [ht]; simp
  let lam : Fin bdA.t → ℝ := fun j => (bdA.r j : ℝ) / (bdA.s j : ℝ)
  have hlam_pos : ∀ j, 0 < lam j := fun j =>
   div_pos (Nat.cast_pos.mpr (bdA.hr j)) (Nat.cast_pos.mpr (bdA.hs j))
  let M : ℝ := 1 + 2 * ∑ j : Fin bdA.t, lam j
  have hM_pos : 0 < M := by
   dsimp only [M]
   have : 0 ≤ ∑ j : Fin bdA.t, lam j := sum_nonneg fun j _ => le_of_lt (hlam_pos j)
   linarith
  let f : ℝ → ℝ := fun t => W⁻¹ * ∑ j : Fin bdA.t, bFn t (lam j) * w j
  have hf_cont : ContinuousOn f (Set.Icc 0 M) := by
   dsimp only [f]
   refine ContinuousOn.mul continuousOn_const (continuousOn_finsetSum _ fun j _ => ?_)
   refine ContinuousOn.mul ?_ continuousOn_const
   dsimp only [bFn]
   exact ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
    fun t ht => ne_of_gt (by linarith [hlam_pos j, ht.1])
  have hf0 : f 0 = 1 := by
   dsimp only [f, bFn]
   have hterm : ∀ j : Fin bdA.t, lam j / (lam j + 0) * w j = w j := fun j => by
    rw [add_zero, div_self (ne_of_gt (hlam_pos j)), one_mul]
   simp_rw [hterm, hw_sum]
   exact inv_mul_cancel₀ (ne_of_gt hW_pos)
  have hfM : f M ≤ 1 / 2 := by
   dsimp only [f]
   have hterm : ∀ j : Fin bdA.t, bFn M (lam j) * w j ≤ (1 / 2) * w j := fun j => by
    refine mul_le_mul_of_nonneg_right ?_ (hw_nn j)
    dsimp only [bFn]
    have hle_sum : lam j ≤ ∑ j' : Fin bdA.t, lam j' :=
     single_le_sum (fun j' _ => le_of_lt (hlam_pos j')) (mem_univ j)
    have hM_gt : 2 * lam j < M := by dsimp only [M]; linarith
    rw [div_le_iff₀ (by linarith [hlam_pos j, hM_pos])]
    linarith
   calc
    W⁻¹ * ∑ j : Fin bdA.t, bFn M (lam j) * w j
     ≤ W⁻¹ * ∑ j : Fin bdA.t, (1 / 2) * w j :=
       mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => hterm j)
        (inv_nonneg.mpr (le_of_lt hW_pos))
    _ = 1 / 2 := by
       rw [← Finset.mul_sum, hw_sum, ← mul_assoc, mul_comm W⁻¹ (1 / 2), mul_assoc,
        inv_mul_cancel₀ (ne_of_gt hW_pos), mul_one]
  have hmem : (1 / 2 : ℝ) ∈ Set.Icc (f M) (f 0) := ⟨hfM, by linarith⟩
  obtain ⟨t, htI, hft⟩ := intermediate_value_Icc' (le_of_lt hM_pos) hf_cont hmem
  have ht_pos : 0 < t := lt_of_le_of_ne htI.1 fun h0 => by
   rw [← h0, hf0] at hft; norm_num at hft
  exact ⟨t, ht_pos, hft⟩
 choose mu hmu_pos hmu_eq using hmu_ex
 refine ⟨mu, hmu_pos, ?_, ?_, ?_⟩
 ·
  exact A.sum_mem fun j _ => A.sum_mem fun k _ =>
   A.smul_mem (A.mul_mem (cPr_mem bdA j) (hDA (cPr_mem bdD k))) _
 ·
  let P : Fin bdA.t × Fin bdD.t → Matrix (Fin d) (Fin d) ℂ :=
   fun p => cPr bdA p.1 * cPr bdD p.2
  let c : Fin bdA.t × Fin bdD.t → ℝ :=
   fun p => bFn (mu p.2) ((bdA.r p.1 : ℝ) / (bdA.s p.1 : ℝ))
  have hsum_eq : (∑ j : Fin bdA.t, ∑ k : Fin bdD.t,
    (bFn (mu k) ((bdA.r j : ℝ) / (bdA.s j : ℝ)) : ℂ) •
     (cPr bdA j * cPr bdD k)) = ∑ p : Fin bdA.t × Fin bdD.t, (c p : ℂ) • P p :=
   (sum_prod_type (fun p : Fin bdA.t × Fin bdD.t => (c p : ℂ) • P p)).symm
  rw [hsum_eq]
  refine orthog_proj_family_opNorm_le P ?_ ?_ ?_ c zero_le_one ?_
  ·
   intro ⟨j, k⟩; dsimp only [P]
   rw [ctM, cPr_herm, cPr_herm, hcomm]
  ·
   intro ⟨j₁, k₁⟩ ⟨j₂, k₂⟩; dsimp only [P]
   calc
    (cPr bdA j₁ * cPr bdD k₁) * (cPr bdA j₂ * cPr bdD k₂)
     = (cPr bdA j₁ * cPr bdA j₂) * (cPr bdD k₁ * cPr bdD k₂) := by
       rw [mma, ← mma (cPr bdD k₁), ← hcomm j₂ k₁,
        mma, mma]
    _ = if (j₁, k₁) = (j₂, k₂) then cPr bdA j₁ * cPr bdD k₁ else 0 := by
       rw [cPr_mul, cPr_mul]
       by_cases hj : j₁ = j₂ <;> by_cases hk : k₁ = k₂ <;> simp [hj, hk]
  ·
   rw [sum_prod_type]
   simp_rw [P, ← Matrix.mul_sum, sum_cPr, mm1, sum_cPr]
  ·
   intro ⟨j, k⟩; dsimp only [c]
   have hlam : 0 < (bdA.r j : ℝ) / (bdA.s j : ℝ) :=
    div_pos (Nat.cast_pos.mpr (bdA.hr j)) (Nat.cast_pos.mpr (bdA.hs j))
   rw [abs_of_pos (betaFn_pos (hmu_pos k) hlam)]
   exact le_of_lt (betaFn_lt_one (hmu_pos k) hlam)
 ·
  rw [map_sum]
  have hinner : ∀ j : Fin bdA.t,
    cExp D (∑ k : Fin bdD.t,
     (bFn (mu k) ((bdA.r j : ℝ) / (bdA.s j : ℝ)) : ℂ) •
      (cPr bdA j * cPr bdD k)) =
    ∑ k : Fin bdD.t,
     ((bFn (mu k) ((bdA.r j : ℝ) / (bdA.s j : ℝ)) *
      (((cPr bdA j * cPr bdD k).trace).re /
       ((bdD.r k * bdD.s k : ℕ) : ℝ)) : ℝ) : ℂ) • cPr bdD k := by
   intro j
   rw [map_sum]
   refine sum_congr rfl fun k _ => ?_
   rw [LinearMap.map_smul, condExp_centralProj_mul_eq hDA bdD bdA j k, smul_smul]
   congr 1; push_cast; ring
  simp_rw [hinner]
  rw [sum_comm]
  have houter : ∀ k : Fin bdD.t,
    (∑ j : Fin bdA.t,
     ((bFn (mu k) ((bdA.r j : ℝ) / (bdA.s j : ℝ)) *
      (((cPr bdA j * cPr bdD k).trace).re /
       ((bdD.r k * bdD.s k : ℕ) : ℝ)) : ℝ) : ℂ) • cPr bdD k) =
    ((1 / 2 : ℝ) : ℂ) • cPr bdD k := by
   intro k
   rw [← Finset.sum_smul, ← Complex.ofReal_sum]
   congr 2
   have hfactor : ∑ j : Fin bdA.t,
     bFn (mu k) ((bdA.r j : ℝ) / (bdA.s j : ℝ)) *
      (((cPr bdA j * cPr bdD k).trace).re / ((bdD.r k * bdD.s k : ℕ) : ℝ)) =
     ((bdD.r k * bdD.s k : ℕ) : ℝ)⁻¹ *
      ∑ j : Fin bdA.t,
       bFn (mu k) ((bdA.r j : ℝ) / (bdA.s j : ℝ)) *
        ((cPr bdA j * cPr bdD k).trace).re := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun j _ => by ring
   rw [hfactor, hmu_eq k]
  simp_rw [houter, ← Finset.smul_sum, sum_cPr]
lemma no_drift_delta_le {d : ℕ}
  {D A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdD : BDec D) (bdA : BDec A)
  {u : Matrix (Fin d) (Fin d) ℂ} (huU : u ∈ unitaryGroup (Fin d) ℂ)
  {ε : ℝ} (hε : 0 ≤ ε)
  (mu : Fin bdD.t → ℝ) (hmu : ∀ k, 0 < mu k)
  (bc : BCData (conjBD bdA u huU) bdA ε)
  (P : Fin (conjBD bdA u huU).t × Fin bdA.t × Fin bdD.t → Matrix (Fin bc.m) (Fin bc.m) ℂ)
  (hP_def : ∀ i j k, P (i, j, k) =
   bc.πB (cPr (conjBD bdA u huU) i) *
   bc.πA' (cPr bdA j) * bc.πB (cPr bdD k))
  (hPh : ∀ p, (P p)ᴴ = P p)
  (hPmul : ∀ p q, P p * P q = if p = q then P p else 0)
  (hPsum : ∑ p, P p = 1)
  (hw_nn : ∀ p, 0 ≤ ((P p).trace).re)
  (hsum_πB : ∀ {α : Type} [DecidableEq α] (s : Finset α) (f : α → Matrix (Fin d) (Fin d) ℂ),
   bc.πB (∑ a ∈ s, f a) = ∑ a ∈ s, bc.πB (f a))
  (cM cP : Fin (conjBD bdA u huU).t × Fin bdA.t × Fin bdD.t → ℝ)
  (hcM_def : ∀ p, cM p = if 0 < bc.q' p.1 then
   bFn (mu p.2.2) (((conjBD bdA u huU).r p.1 : ℝ) / (bc.q' p.1 : ℝ)) else 0)
  (hcP_def : ∀ p, cP p = if 0 < bc.r' p.2.1 then
   bFn (mu p.2.2) ((bc.r' p.2.1 : ℝ) / (bdA.s p.2.1 : ℝ)) else 0)
  (xM xP : Matrix (Fin bc.m) (Fin bc.m) ℂ)
  (hxM_def : xM = ∑ p, (cM p : ℂ) • P p)
  (hxP_def : xP = ∑ p, (cP p : ℂ) • P p)
  (hcM_le_cP : ∀ p, P p ≠ 0 → 0 < bc.q' p.1 ∧ 0 < bc.r' p.2.1 ∧ 0 < cM p ∧ cM p ≤ cP p ∧ cP p < 1)
  {η : ℝ} (hη : 0 ≤ η)
  (hxP_half : hsN (xP - ((1 / 2 : ℝ) : ℂ) • 1) ≤ (η + 5 * ε) * sqrt (d : ℝ))
  (hxM_half : hsN (xM - ((1 / 2 : ℝ) : ℂ) • 1) ≤
   (η + 5 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * sqrt (d : ℝ)) :
  ∑ i' : Fin bc.bdBhat.t, ∑ j' : Fin bc.bdAhat.t,
   (1 - ((bc.bdBhat.r i' * bc.bdAhat.s j' : ℝ) / (bc.bdBhat.s i' * bc.bdAhat.r j' : ℝ))) *
    ((cPr bc.bdAhat j' * cPr bc.bdBhat i').trace).re ≤
  16 * (2 * η + 10 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * (1 + 2 * ε) * (d : ℝ) := by
 classical
 let bdB := conjBD bdA u huU
 let δ : ℝ := ∑ i' : Fin bc.bdBhat.t, ∑ j' : Fin bc.bdAhat.t,
  (1 - ((bc.bdBhat.r i' * bc.bdAhat.s j' : ℝ) / (bc.bdBhat.s i' * bc.bdAhat.r j' : ℝ))) *
   ((cPr bc.bdAhat j' * cPr bc.bdBhat i').trace).re
 show δ ≤ _
 have hsum_P : ∀ (i' : Fin bc.bdBhat.t) (j' : Fin bc.bdAhat.t),
   cPr bc.bdAhat j' * cPr bc.bdBhat i' =
    ∑ k : Fin bdD.t, P ((bc.eB i').1, (bc.eA j').1, k) := by
  intro i' j'
  simp_rw [hP_def, ← Matrix.mul_sum, ← hsum_πB, sum_cPr, bc.hπB_one, mm1]
  rw [bc.hAhat_z j', bc.hBhat_z i',
   bc.hπ_comm _ (cPr_mem bdB _) _ (cPr_comm bdA _)]
 have hterm_le : ∀ (i' : Fin bc.bdBhat.t) (j' : Fin bc.bdAhat.t),
   (1 - ((bc.bdBhat.r i' * bc.bdAhat.s j' : ℝ) / (bc.bdBhat.s i' * bc.bdAhat.r j' : ℝ))) *
    ((cPr bc.bdAhat j' * cPr bc.bdBhat i').trace).re ≤
   ∑ k : Fin bdD.t,
    16 * (|cM ((bc.eB i').1, (bc.eA j').1, k) - 1 / 2| +
     |cP ((bc.eB i').1, (bc.eA j').1, k) - 1 / 2|) *
     ((P ((bc.eB i').1, (bc.eA j').1, k)).trace).re := by
  intro i' j'
  rw [hsum_P i' j', trace_sum, re_sum, Finset.mul_sum]
  refine sum_le_sum fun k _ => ?_
  let p : Fin bdB.t × Fin bdA.t × Fin bdD.t := ((bc.eB i').1, (bc.eA j').1, k)
  by_cases h0 : P p = 0
  · rw [h0, trace_zero, zero_re, mul_zero, mul_zero]
  ·
   refine mul_le_mul_of_nonneg_right ?_ (hw_nn p)
   obtain ⟨hqi, hrj, h1, h2, h3⟩ := hcM_le_cP p h0
   have hrat : (bc.bdBhat.r i' * bc.bdAhat.s j' : ℝ) / (bc.bdBhat.s i' * bc.bdAhat.r j' : ℝ) =
     (cM p * (1 - cP p)) / (cP p * (1 - cM p)) := by
    rw [bc.hBhat_r, bc.hBhat_s, bc.hAhat_r, bc.hAhat_s]
    have hlam1 : (0 : ℝ) < (bdB.r (bc.eB i').1 : ℝ) / (bc.q' (bc.eB i').1 : ℝ) :=
     div_pos (Nat.cast_pos.mpr (bdB.hr (bc.eB i').1)) (Nat.cast_pos.mpr hqi)
    have hlam2 : (0 : ℝ) < (bc.r' (bc.eA j').1 : ℝ) / (bdA.s (bc.eA j').1 : ℝ) :=
     div_pos (Nat.cast_pos.mpr hrj) (Nat.cast_pos.mpr (bdA.hs (bc.eA j').1))
    have hbr := betaFn_ratio_eq (hmu k) hlam1 hlam2
    rw [hcM_def, hcP_def]; simp only [p, hqi, hrj, ↓reduceIte]
    rw [hbr]
    have hq0 : (bc.q' (bc.eB i').1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hqi)
    have hr0 : (bc.r' (bc.eA j').1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hrj)
    have hs0 : (bdA.s (bc.eA j').1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (bdA.hs _))
    field_simp [hq0, hr0, hs0]; rfl
   rw [hrat]
   exact ratio_defect_le_abs h1 h2 h3
 have hδ_sum_all : δ ≤ 16 * (∑ p, |cM p - 1 / 2| * ((P p).trace).re +
   ∑ p, |cP p - 1 / 2| * ((P p).trace).re) := by
  dsimp only [δ]
  have hstep1 : ∑ i' : Fin bc.bdBhat.t, ∑ j' : Fin bc.bdAhat.t,
    (1 - ((bc.bdBhat.r i' * bc.bdAhat.s j' : ℝ) / (bc.bdBhat.s i' * bc.bdAhat.r j' : ℝ))) *
     ((cPr bc.bdAhat j' * cPr bc.bdBhat i').trace).re ≤
    ∑ i' : Fin bc.bdBhat.t, ∑ j' : Fin bc.bdAhat.t, ∑ k : Fin bdD.t,
     16 * (|cM ((bc.eB i').1, (bc.eA j').1, k) - 1 / 2| +
      |cP ((bc.eB i').1, (bc.eA j').1, k) - 1 / 2|) *
      ((P ((bc.eB i').1, (bc.eA j').1, k)).trace).re :=
   sum_le_sum fun i' _ => sum_le_sum fun j' _ => hterm_le i' j'
  let g : Fin bdB.t × Fin bdA.t × Fin bdD.t → ℝ :=
   fun p => 16 * (|cM p - 1 / 2| + |cP p - 1 / 2|) * ((P p).trace).re
  have hg_nn : ∀ p, 0 ≤ g p := fun p => by
   dsimp only [g]
   exact mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _))) (hw_nn p)
  have hinj : Function.Injective (fun q : Fin bc.bdBhat.t × Fin bc.bdAhat.t × Fin bdD.t =>
    ((bc.eB q.1).1, (bc.eA q.2.1).1, q.2.2)) := by
   intro ⟨i₁, j₁, k₁⟩ ⟨i₂, j₂, k₂⟩ h
   simp only [Prod.mk.injEq] at h
   rcases h with ⟨hi, hj, hk⟩
   have hi' := bc.eB.injective (Subtype.ext hi)
   have hj' := bc.eA.injective (Subtype.ext hj)
   subst hi' hj' hk; rfl
  have hstep2 : ∑ i' : Fin bc.bdBhat.t, ∑ j' : Fin bc.bdAhat.t, ∑ k : Fin bdD.t,
    g ((bc.eB i').1, (bc.eA j').1, k) ≤ ∑ p, g p := by
   have hprod : ∑ q : Fin bc.bdBhat.t × Fin bc.bdAhat.t × Fin bdD.t,
     g ((bc.eB q.1).1, (bc.eA q.2.1).1, q.2.2) =
     ∑ i' : Fin bc.bdBhat.t, ∑ j' : Fin bc.bdAhat.t, ∑ k : Fin bdD.t,
      g ((bc.eB i').1, (bc.eA j').1, k) := by
    rw [sum_prod_type]
    refine sum_congr rfl fun i' _ => sum_prod_type _
   rw [← hprod]
   calc
    ∑ q : Fin bc.bdBhat.t × Fin bc.bdAhat.t × Fin bdD.t,
      g ((bc.eB q.1).1, (bc.eA q.2.1).1, q.2.2)
     = ∑ p ∈ univ.image (fun q : Fin bc.bdBhat.t × Fin bc.bdAhat.t × Fin bdD.t =>
       ((bc.eB q.1).1, (bc.eA q.2.1).1, q.2.2)), g p :=
      (Finset.sum_image fun x _ y _ h => hinj h).symm
    _ ≤ ∑ p ∈ univ, g p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => hg_nn p
  have hstep3 : ∑ p, g p = 16 * (∑ p, |cM p - 1 / 2| * ((P p).trace).re +
    ∑ p, |cP p - 1 / 2| * ((P p).trace).re) := by
   dsimp only [g]
   rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
   refine sum_congr rfl fun p _ => by ring
  exact hstep1.trans (hstep2.trans_eq hstep3)
 have hsum_w : ∑ p, ((P p).trace).re = (bc.m : ℝ) := by
  rw [← re_sum, ← trace_sum, hPsum, trace_one, card_fin]; simp
 have hsq_M : ∑ p, (cM p - 1 / 2) ^ 2 * ((P p).trace).re =
   hsSq (xM - ((1 / 2 : ℝ) : ℂ) • 1) := by
  have h1 : xM - ((1 / 2 : ℝ) : ℂ) • 1 = ∑ p, ((cM p - 1 / 2 : ℝ) : ℂ) • P p := by
   rw [hxM_def]; conv_lhs => rhs; rw [← hPsum, Finset.smul_sum]
   rw [← sum_sub_distrib]
   refine sum_congr rfl fun p _ => by rw [← sub_smul, ofReal_sub]
  rw [h1, orthog_proj_family_hsSq P hPh hPmul]
 have hsq_P : ∑ p, (cP p - 1 / 2) ^ 2 * ((P p).trace).re =
   hsSq (xP - ((1 / 2 : ℝ) : ℂ) • 1) := by
  have h1 : xP - ((1 / 2 : ℝ) : ℂ) • 1 = ∑ p, ((cP p - 1 / 2 : ℝ) : ℂ) • P p := by
   rw [hxP_def]; conv_lhs => rhs; rw [← hPsum, Finset.smul_sum]
   rw [← sum_sub_distrib]
   refine sum_congr rfl fun p _ => by rw [← sub_smul, ofReal_sub]
  rw [h1, orthog_proj_family_hsSq P hPh hPmul]
 have hcsM : ∑ p, |cM p - 1 / 2| * ((P p).trace).re ≤
   hsN (xM - ((1 / 2 : ℝ) : ℂ) • 1) * sqrt (bc.m : ℝ) := by
  have h := weighted_cs (fun p => cM p - 1 / 2) (fun p => ((P p).trace).re) hw_nn
  rwa [hsq_M, hsum_w] at h
 have hcsP : ∑ p, |cP p - 1 / 2| * ((P p).trace).re ≤
   hsN (xP - ((1 / 2 : ℝ) : ℂ) • 1) * sqrt (bc.m : ℝ) := by
  have h := weighted_cs (fun p => cP p - 1 / 2) (fun p => ((P p).trace).re) hw_nn
  rwa [hsq_P, hsum_w] at h
 have hsqrt_m : sqrt (bc.m : ℝ) ≤ (1 + 2 * ε) * sqrt (d : ℝ) := by
  have hm_le : (bc.m : ℝ) ≤ ((1 + 2 * ε) * sqrt (d : ℝ)) ^ 2 := by
   have h1 : (bc.m : ℝ) - (d : ℝ) ≤ 2 * ε ^ 2 * (d : ℝ) := (le_abs_self _).trans bc.hm_diff
   rw [mul_pow, sq_sqrt (Nat.cast_nonneg d)]
   nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hrt := sqrt_le_sqrt hm_le
  rwa [sqrt_sq (by positivity)] at hrt
 calc
  δ ≤ 16 * ((hsN (xM - ((1 / 2 : ℝ) : ℂ) • 1) + hsN (xP - ((1 / 2 : ℝ) : ℂ) • 1)) *
    sqrt (bc.m : ℝ)) := by linarith
  _ ≤ 16 * (((2 * η + 10 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * sqrt (d : ℝ)) *
    ((1 + 2 * ε) * sqrt (d : ℝ))) := by
    gcongr
    · linarith
  _ = 16 * (2 * η + 10 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * (1 + 2 * ε) *
    (sqrt (d : ℝ) * sqrt (d : ℝ)) := by ring
  _ = 16 * (2 * η + 10 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * (1 + 2 * ε) * (d : ℝ) := by
    rw [mul_self_sqrt (Nat.cast_nonneg d)]
lemma no_drift_partB {d : ℕ}
  {D A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdD : BDec D) (bdA : BDec A)
  {u : Matrix (Fin d) (Fin d) ℂ} (huU : u ∈ unitaryGroup (Fin d) ℂ)
  {ε : ℝ} (hε : 0 ≤ ε)
  (mu : Fin bdD.t → ℝ) (hmu : ∀ k, 0 < mu k)
  (bc : BCData (conjBD bdA u huU) bdA ε)
  (P : Fin (conjBD bdA u huU).t × Fin bdA.t × Fin bdD.t → Matrix (Fin bc.m) (Fin bc.m) ℂ)
  (hP_def : ∀ i j k, P (i, j, k) =
   bc.πB (cPr (conjBD bdA u huU) i) *
   bc.πA' (cPr bdA j) * bc.πB (cPr bdD k))
  (hPh : ∀ p, (P p)ᴴ = P p)
  (hPmul : ∀ p q, P p * P q = if p = q then P p else 0)
  (hPsum : ∑ p, P p = 1)
  (hw_nn : ∀ p, 0 ≤ ((P p).trace).re)
  (hsum_πB : ∀ {α : Type} [DecidableEq α] (s : Finset α) (f : α → Matrix (Fin d) (Fin d) ℂ),
   bc.πB (∑ a ∈ s, f a) = ∑ a ∈ s, bc.πB (f a))
  (cM cTP cP : Fin (conjBD bdA u huU).t × Fin bdA.t × Fin bdD.t → ℝ)
  (hcM_def : ∀ p, cM p = if 0 < bc.q' p.1 then
   bFn (mu p.2.2) (((conjBD bdA u huU).r p.1 : ℝ) / (bc.q' p.1 : ℝ)) else 0)
  (hcTP_def : ∀ p, cTP p = bFn (mu p.2.2) ((bdA.r p.2.1 : ℝ) / (bdA.s p.2.1 : ℝ)))
  (hcP_def : ∀ p, cP p = if 0 < bc.r' p.2.1 then
   bFn (mu p.2.2) ((bc.r' p.2.1 : ℝ) / (bdA.s p.2.1 : ℝ)) else 0)
  (x : Matrix (Fin d) (Fin d) ℂ)
  (xM xTP xP : Matrix (Fin bc.m) (Fin bc.m) ℂ)
  (hxM_def : xM = ∑ p, (cM p : ℂ) • P p)
  (hxTP_def : xTP = ∑ p, (cTP p : ℂ) • P p)
  (hxP_def : xP = ∑ p, (cP p : ℂ) • P p)
  (hxTP_W : xTP * bc.W = bc.W * x)
  (h1W'W_norm : hsN (1 - bc.Wᴴ * bc.W) ≤ 2 * ε * sqrt (d : ℝ))
  (h1WW_norm : hsN (1 - bc.W * bc.Wᴴ) ≤ 2 * ε * sqrt (d : ℝ))
  (hTP_P_norm : hsN (xTP - xP) ≤ 3 * ε * sqrt (d : ℝ))
  (hP_M_norm : hsN (xP - xM) ≤ sqrt (6 * ε + 26 * ε ^ 2) * sqrt (d : ℝ))
  (hcM_le_cP : ∀ p, P p ≠ 0 → 0 < bc.q' p.1 ∧ 0 < bc.r' p.2.1 ∧ 0 < cM p ∧ cM p ≤ cP p ∧ cP p < 1)
  {η : ℝ} (hη : 0 ≤ η) (hx_half : hsSq (x - ((1 / 2 : ℝ) : ℂ) • 1) ≤ η ^ 2 * (d : ℝ))
  {a : Matrix (Fin d) (Fin d) ℂ} (ha : a ∈ A) (ha_norm : ‖CLM a‖ ≤ 1) :
  hsN (a - cExp (conjAlg u huU A) a) ≤
   (sqrt (128 * (2 * η + 10 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * (1 + 2 * ε)) +
    12 * ε) * sqrt (d : ℝ) := by
 classical
 let B := conjAlg u huU A
 have hW_src_conj : (bc.Wᴴᴴ * bc.Wᴴ) * (bc.Wᴴᴴ * bc.Wᴴ) = bc.Wᴴᴴ * bc.Wᴴ := by
  simpa [ctct] using bc.hW_tgt
 have hW_tgt_conj : (bc.Wᴴ * bc.Wᴴᴴ) * (bc.Wᴴ * bc.Wᴴᴴ) = bc.Wᴴ * bc.Wᴴᴴ := by
  simpa [ctct] using bc.hW_src
 have hx_half_norm : hsN (x - ((1 / 2 : ℝ) : ℂ) • 1) ≤ η * sqrt (d : ℝ) := by
  have hrt := sqrt_le_sqrt hx_half
  rwa [sqrt_mul (sq_nonneg η), sqrt_sq hη] at hrt
 have hxTP_half_norm : hsN (xTP - ((1 / 2 : ℝ) : ℂ) • 1) ≤ (η + 2 * ε) * sqrt (d : ℝ) := by
  have hsplit : xTP - ((1 / 2 : ℝ) : ℂ) • 1 =
    bc.W * (x - ((1 / 2 : ℝ) : ℂ) • 1) * bc.Wᴴ +
     (xTP - ((1 / 2 : ℝ) : ℂ) • 1) * (1 - bc.W * bc.Wᴴ) := by
   have h1 : bc.W * (x - ((1 / 2 : ℝ) : ℂ) • 1) * bc.Wᴴ =
     (xTP - ((1 / 2 : ℝ) : ℂ) • 1) * (bc.W * bc.Wᴴ) := by
    rw [mms, msm, msm, Matrix.mul_smul, Matrix.smul_mul,
     Matrix.smul_mul, mm1, m1m, ← hxTP_W, mma]
   rw [h1, mms, mm1]; abel
  have h1 : hsN (bc.W * (x - ((1 / 2 : ℝ) : ℂ) • 1) * bc.Wᴴ) ≤ η * sqrt (d : ℝ) :=
   (hsN_piR bc.Wᴴ hW_tgt_conj _).trans
    ((hsN_piL bc.W bc.hW_src _).trans hx_half_norm)
  have h2 : hsN ((xTP - ((1 / 2 : ℝ) : ℂ) • 1) * (1 - bc.W * bc.Wᴴ)) ≤ 2 * ε * sqrt (d : ℝ) := by
   let X : Matrix (Fin bc.m) (Fin bc.m) ℂ := xTP - ((1 / 2 : ℝ) : ℂ) • 1
   have hclm : ‖CLM X‖ ≤ 1 := by
    have heq : X = ∑ p, ((cTP p - 1 / 2 : ℝ) : ℂ) • P p := by
     dsimp only [X]; rw [hxTP_def]
     conv_lhs => rhs; rw [← hPsum, Finset.smul_sum]
     rw [← sum_sub_distrib]
     refine sum_congr rfl fun p _ => by rw [← sub_smul, ofReal_sub]
    rw [heq]
    refine orthog_proj_family_opNorm_le P hPh hPmul hPsum _ zero_le_one fun ⟨i, j, k⟩ => ?_
    rw [hcTP_def]
    have hlam : (0 : ℝ) < (bdA.r j : ℝ) / (bdA.s j : ℝ) :=
     div_pos (Nat.cast_pos.mpr (bdA.hr j)) (Nat.cast_pos.mpr (bdA.hs j))
    have h1 := betaFn_pos (hmu k) hlam
    have h2 := betaFn_lt_one (hmu k) hlam
    rw [abs_le]; constructor <;> linarith
   calc
    hsN (X * (1 - bc.W * bc.Wᴴ))
     ≤ ‖CLM X‖ * hsN (1 - bc.W * bc.Wᴴ) := hsN_mulL X _
    _ ≤ 1 * (2 * ε * sqrt (d : ℝ)) :=
      mul_le_mul hclm h1WW_norm (hsN_nn _) zero_le_one
    _ = 2 * ε * sqrt (d : ℝ) := one_mul _
  rw [hsplit]
  calc
   hsN _ ≤ hsN (bc.W * (x - ((1 / 2 : ℝ) : ℂ) • 1) * bc.Wᴴ) +
     hsN ((xTP - ((1 / 2 : ℝ) : ℂ) • 1) * (1 - bc.W * bc.Wᴴ)) := hsN_add _ _
   _ ≤ (η + 2 * ε) * sqrt (d : ℝ) := by linarith
 have hxP_half : hsN (xP - ((1 / 2 : ℝ) : ℂ) • 1) ≤ (η + 5 * ε) * sqrt (d : ℝ) := by
  have h1 : xP - ((1 / 2 : ℝ) : ℂ) • 1 = (xTP - ((1 / 2 : ℝ) : ℂ) • 1) - (xTP - xP) := by abel
  rw [h1]
  exact (hsN_sub _ _).trans (by linarith)
 have hxM_half : hsN (xM - ((1 / 2 : ℝ) : ℂ) • 1) ≤
   (η + 5 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * sqrt (d : ℝ) := by
  have h1 : xM - ((1 / 2 : ℝ) : ℂ) • 1 = (xP - ((1 / 2 : ℝ) : ℂ) • 1) - (xP - xM) := by abel
  rw [h1]
  exact (hsN_sub _ _).trans (by linarith)
 have hδ_le := no_drift_delta_le bdD bdA huU hε mu hmu bc P hP_def hPh hPmul hPsum hw_nn hsum_πB
  cM cP hcM_def hcP_def xM xP hxM_def hxP_def hcM_le_cP hη hxP_half hxM_half
 let ahat : Matrix (Fin bc.m) (Fin bc.m) ℂ := bc.W * a * bc.Wᴴ
 have hahat : ahat ∈ bc.Ahat := bc.hW_conj_A a ha
 have hahat_n : ‖CLM ahat‖ ≤ 1 :=
  (opN_conjPI bc.W bc.hW_src a).trans ha_norm
 have hrev := reverse_scale_estimate bc.hBAhat bc.bdBhat bc.bdAhat hahat hahat_n
 let bhat := cExp bc.Bhat ahat
 have hbhat_mem : bhat ∈ bc.Bhat := condExp_mem bc.Bhat ahat
 have hbhat_n : ‖CLM bhat‖ ≤ 1 := (opNorm_condExp_le bc.Bhat ahat).trans hahat_n
 obtain ⟨b, hbB, hbn, hbπ⟩ := bc.hBhat_lift bhat hbhat_mem
 have hbn1 : ‖CLM b‖ ≤ 1 := hbn.trans hbhat_n
 have hab_le : hsN (a - cExp B a) ≤ hsN (a - b) :=
  sqrt_le_sqrt (hsSq_sub_condExp_le B a hbB)
 have hsplit : a - b =
   bc.Wᴴ * (ahat - bhat) * bc.W + bc.Wᴴ * (bc.πB b * bc.W - bc.W * b) +
   (1 - bc.Wᴴ * bc.W) * a + (bc.Wᴴ * bc.W) * (a * (1 - bc.Wᴴ * bc.W)) -
   (1 - bc.Wᴴ * bc.W) * b := by
  dsimp only [ahat]
  rw [hbπ]
  simp only [mms, msm, mm1, m1m, mma]
  abel
 have ht1 : hsN (bc.Wᴴ * (ahat - bhat) * bc.W) ≤
   sqrt (128 * (2 * η + 10 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * (1 + 2 * ε)) *
    sqrt (d : ℝ) := by
  have h1 : hsN (bc.Wᴴ * (ahat - bhat) * bc.W) ≤ hsN (ahat - bhat) :=
   (hsN_piR bc.W bc.hW_tgt _).trans
    (hsN_piL bc.Wᴴ hW_src_conj _)
  have h2 : hsSq (ahat - bhat) ≤
    128 * (2 * η + 10 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * (1 + 2 * ε) * (d : ℝ) := by
   linarith
  have hrt := sqrt_le_sqrt h2
  rw [sqrt_mul (by positivity)] at hrt
  exact h1.trans hrt
 have ht2 : hsN (bc.Wᴴ * (bc.πB b * bc.W - bc.W * b)) ≤ 6 * ε * sqrt (d : ℝ) :=
  (hsN_piL bc.Wᴴ hW_src_conj _).trans (bc.hW_approx_B b hbB hbn1)
 have ht3 : hsN ((1 - bc.Wᴴ * bc.W) * a) ≤ 2 * ε * sqrt (d : ℝ) :=
  (hsN_mulR _ a).trans
   (by nlinarith [h1W'W_norm, hsN_nn (1 - bc.Wᴴ * bc.W)])
 have ht4 : hsN ((bc.Wᴴ * bc.W) * (a * (1 - bc.Wᴴ * bc.W))) ≤ 2 * ε * sqrt (d : ℝ) := by
  have hPh : (bc.Wᴴ * bc.W)ᴴ = bc.Wᴴ * bc.W := by simp
  calc
   hsN ((bc.Wᴴ * bc.W) * (a * (1 - bc.Wᴴ * bc.W)))
    ≤ hsN (a * (1 - bc.Wᴴ * bc.W)) :=
      sqrt_le_sqrt (hsSq_proj_mul_le (bc.Wᴴ * bc.W) hPh bc.hW_src _)
   _ ≤ ‖CLM a‖ * hsN (1 - bc.Wᴴ * bc.W) := hsN_mulL a _
   _ ≤ 2 * ε * sqrt (d : ℝ) := by nlinarith [h1W'W_norm, hsN_nn (1 - bc.Wᴴ * bc.W)]
 have ht5 : hsN ((1 - bc.Wᴴ * bc.W) * b) ≤ 2 * ε * sqrt (d : ℝ) :=
  (hsN_mulR _ b).trans
   (by nlinarith [h1W'W_norm, hsN_nn (1 - bc.Wᴴ * bc.W)])
 refine hab_le.trans ?_
 rw [hsplit]
 have htri1 := hsN_sub
  (bc.Wᴴ * (ahat - bhat) * bc.W + bc.Wᴴ * (bc.πB b * bc.W - bc.W * b) +
   (1 - bc.Wᴴ * bc.W) * a + (bc.Wᴴ * bc.W) * (a * (1 - bc.Wᴴ * bc.W)))
  ((1 - bc.Wᴴ * bc.W) * b)
 have htri2 := hsN_add
  (bc.Wᴴ * (ahat - bhat) * bc.W + bc.Wᴴ * (bc.πB b * bc.W - bc.W * b) + (1 - bc.Wᴴ * bc.W) * a)
  ((bc.Wᴴ * bc.W) * (a * (1 - bc.Wᴴ * bc.W)))
 have htri3 := hsN_add
  (bc.Wᴴ * (ahat - bhat) * bc.W + bc.Wᴴ * (bc.πB b * bc.W - bc.W * b))
  ((1 - bc.Wᴴ * bc.W) * a)
 have htri4 := hsN_add
  (bc.Wᴴ * (ahat - bhat) * bc.W)
  (bc.Wᴴ * (bc.πB b * bc.W - bc.W * b))
 linarith
lemma no_drift_xTM_xTP_bounds {d : ℕ}
  {D A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  (bdD : BDec D) (bdA : BDec A)
  {u : Matrix (Fin d) (Fin d) ℂ} (huU : u ∈ unitaryGroup (Fin d) ℂ)
  {ε : ℝ}
  (mu : Fin bdD.t → ℝ) (hmu : ∀ k, 0 < mu k)
  (bc : BCData (conjBD bdA u huU) bdA ε)
  (P : Fin (conjBD bdA u huU).t × Fin bdA.t × Fin bdD.t → Matrix (Fin bc.m) (Fin bc.m) ℂ)
  (hP_def : ∀ i j k, P (i, j, k) =
   bc.πB (cPr (conjBD bdA u huU) i) *
   bc.πA' (cPr bdA j) * bc.πB (cPr bdD k))
  (hPh : ∀ p, (P p)ᴴ = P p)
  (hPmul : ∀ p q, P p * P q = if p = q then P p else 0)
  (hw_nn : ∀ p, 0 ≤ ((P p).trace).re)
  (hw_sum_i : ∀ i : Fin (conjBD bdA u huU).t,
   ∑ j : Fin bdA.t, ∑ k : Fin bdD.t, ((P (i, j, k)).trace).re =
    ((conjBD bdA u huU).r i : ℝ) * (bc.q' i : ℝ))
  (hw_sum_j : ∀ j : Fin bdA.t,
   ∑ i : Fin (conjBD bdA u huU).t, ∑ k : Fin bdD.t, ((P (i, j, k)).trace).re =
    (bc.r' j : ℝ) * (bdA.s j : ℝ))
  (cTM cM cTP cP : Fin (conjBD bdA u huU).t × Fin bdA.t × Fin bdD.t → ℝ)
  (hcTM_def : ∀ p, cTM p = bFn (mu p.2.2) (((conjBD bdA u huU).r p.1 : ℝ) / ((conjBD bdA u huU).s p.1 : ℝ)))
  (hcM_def : ∀ p, cM p = if 0 < bc.q' p.1 then bFn (mu p.2.2) (((conjBD bdA u huU).r p.1 : ℝ) / (bc.q' p.1 : ℝ)) else 0)
  (hcTP_def : ∀ p, cTP p = bFn (mu p.2.2) ((bdA.r p.2.1 : ℝ) / (bdA.s p.2.1 : ℝ)))
  (hcP_def : ∀ p, cP p = if 0 < bc.r' p.2.1 then bFn (mu p.2.2) ((bc.r' p.2.1 : ℝ) / (bdA.s p.2.1 : ℝ)) else 0)
  (xTM xM xTP xP : Matrix (Fin bc.m) (Fin bc.m) ℂ)
  (hxTM_def : xTM = ∑ p, (cTM p : ℂ) • P p)
  (hxM_def : xM = ∑ p, (cM p : ℂ) • P p)
  (hxTP_def : xTP = ∑ p, (cTP p : ℂ) • P p)
  (hxP_def : xP = ∑ p, (cP p : ℂ) • P p) :
  (hsSq (xTM - xM) ≤ 8 * ε ^ 2 * (d : ℝ) ∧ |((xTM - xM).trace).re| ≤ 8 * ε ^ 2 * (d : ℝ)) ∧
  (hsSq (xTP - xP) ≤ 6 * ε ^ 2 * (d : ℝ) ∧ |((xTP - xP).trace).re| ≤ 6 * ε ^ 2 * (d : ℝ)) := by
 let bdB := conjBD bdA u huU
 let Idx := Fin bdB.t × Fin bdA.t × Fin bdD.t
 constructor
 ·
  have hdiff : xTM - xM = ∑ p : Idx, ((cTM p - cM p : ℝ) : ℂ) • P p := by
   rw [hxTM_def, hxM_def, ← sum_sub_distrib]
   refine sum_congr rfl fun p _ => by rw [← sub_smul, ofReal_sub]
  have hpt : ∀ p : Idx, |cTM p - cM p| * ((P p).trace).re ≤
    (if 0 < bc.q' p.1 then |(bc.q' p.1 : ℝ) - (bdB.s p.1 : ℝ)| / (bc.q' p.1 : ℝ) else 0) *
     ((P p).trace).re := by
   intro ⟨i, j, k⟩
   by_cases hq : 0 < bc.q' i
   ·
    refine mul_le_mul_of_nonneg_right ?_ (hw_nn (i, j, k))
    rw [hcTM_def, hcM_def]; simp only [hq, ↓reduceIte]
    exact abs_betaFn_sub_s_le (hmu k) (Nat.cast_pos.mpr (bdB.hr i))
     (Nat.cast_pos.mpr (bdB.hs i)) (Nat.cast_pos.mpr hq)
   ·
    have hq0 : bc.q' i = 0 := Nat.eq_zero_of_not_pos hq
    have hP0 : P (i, j, k) = 0 := by
     rw [hP_def, bc.hBhat_zero i hq0, Matrix.zero_mul, Matrix.zero_mul]
    rw [hP0, trace_zero, zero_re, mul_zero, mul_zero]
  have hpt_le1 : ∀ p : Idx, 0 < bc.q' p.1 → |cTM p - cM p| ≤ 1 := by
   intro ⟨i, j, k⟩ hq
   rw [hcTM_def, hcM_def]; simp only [hq, ↓reduceIte]
   have h1 := betaFn_pos (hmu k) (div_pos (Nat.cast_pos.mpr (bdB.hr i)) (Nat.cast_pos.mpr (bdB.hs i)))
   have h2 := betaFn_lt_one (hmu k) (div_pos (Nat.cast_pos.mpr (bdB.hr i)) (Nat.cast_pos.mpr (bdB.hs i)))
   have h3 := betaFn_pos (hmu k) (div_pos (Nat.cast_pos.mpr (bdB.hr i)) (Nat.cast_pos.mpr hq))
   have h4 := betaFn_lt_one (hmu k) (div_pos (Nat.cast_pos.mpr (bdB.hr i)) (Nat.cast_pos.mpr hq))
   rw [abs_le]; constructor <;> linarith
  have hsum_abs : ∑ p : Idx, |cTM p - cM p| * ((P p).trace).re ≤ 8 * ε ^ 2 * (d : ℝ) := by
   calc
    ∑ p : Idx, |cTM p - cM p| * ((P p).trace).re
     ≤ ∑ p : Idx, (if 0 < bc.q' p.1 then |(bc.q' p.1 : ℝ) - (bdB.s p.1 : ℝ)| / (bc.q' p.1 : ℝ) else 0) *
       ((P p).trace).re := sum_le_sum fun p _ => hpt p
    _ = ∑ i : Fin bdB.t,
       (if 0 < bc.q' i then |(bc.q' i : ℝ) - (bdB.s i : ℝ)| / (bc.q' i : ℝ) else 0) *
       (∑ j : Fin bdA.t, ∑ k : Fin bdD.t, ((P (i, j, k)).trace).re) := by
       rw [sum_prod_type]
       refine sum_congr rfl fun i _ => by
        rw [sum_prod_type, Finset.mul_sum]
        refine sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin bdB.t, (bdB.r i : ℝ) * |(bc.q' i : ℝ) - (bdB.s i : ℝ)| := by
       refine sum_le_sum fun i _ => ?_
       rw [hw_sum_i i]
       by_cases hq : 0 < bc.q' i
       ·
        simp only [hq, ↓reduceIte]
        have hq0 : (bc.q' i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
        have : |(bc.q' i : ℝ) - (bdB.s i : ℝ)| / (bc.q' i : ℝ) * ((bdB.r i : ℝ) * (bc.q' i : ℝ)) =
          (bdB.r i : ℝ) * |(bc.q' i : ℝ) - (bdB.s i : ℝ)| := by field_simp [hq0]
        linarith
       ·
        simp only [hq, ↓reduceIte, zero_mul]
        exact mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
    _ ≤ 8 * ε ^ 2 * (d : ℝ) := bc.hB_mult
  constructor
  ·
   rw [hdiff, orthog_proj_family_hsSq P hPh hPmul]
   refine (sum_le_sum fun p _ => ?_).trans hsum_abs
   by_cases hq : 0 < bc.q' p.1
   ·
    have hle1 := hpt_le1 p hq
    have hsq : (cTM p - cM p) ^ 2 ≤ |cTM p - cM p| := by
     rw [← sq_abs]; nlinarith [abs_nonneg (cTM p - cM p)]
    exact mul_le_mul_of_nonneg_right hsq (hw_nn p)
   ·
    have hq0 : bc.q' p.1 = 0 := Nat.eq_zero_of_not_pos hq
    have hP0 : P p = 0 := by
     rw [hP_def, bc.hBhat_zero p.1 hq0, Matrix.zero_mul, Matrix.zero_mul]
    rw [hP0, trace_zero, zero_re, mul_zero, mul_zero]
  ·
   rw [hdiff, orthog_proj_family_trace_re]
   calc
    |∑ p : Idx, (cTM p - cM p) * ((P p).trace).re|
     ≤ ∑ p : Idx, |(cTM p - cM p) * ((P p).trace).re| := abs_sum_le_sum_abs _ _
    _ = ∑ p : Idx, |cTM p - cM p| * ((P p).trace).re :=
       sum_congr rfl fun p _ => by rw [abs_mul, abs_of_nonneg (hw_nn p)]
    _ ≤ 8 * ε ^ 2 * (d : ℝ) := hsum_abs
 ·
  have hdiff : xTP - xP = ∑ p : Idx, ((cTP p - cP p : ℝ) : ℂ) • P p := by
   rw [hxTP_def, hxP_def, ← sum_sub_distrib]
   refine sum_congr rfl fun p _ => by rw [← sub_smul, ofReal_sub]
  have hpt : ∀ p : Idx, |cTP p - cP p| * ((P p).trace).re ≤
    (if 0 < bc.r' p.2.1 then |(bc.r' p.2.1 : ℝ) - (bdA.r p.2.1 : ℝ)| / (bc.r' p.2.1 : ℝ) else 0) *
     ((P p).trace).re := by
   intro ⟨i, j, k⟩
   by_cases hr : 0 < bc.r' j
   ·
    refine mul_le_mul_of_nonneg_right ?_ (hw_nn (i, j, k))
    rw [hcTP_def, hcP_def]; simp only [hr, ↓reduceIte]
    exact abs_betaFn_sub_r_le (hmu k) (Nat.cast_pos.mpr (bdA.hr j))
     (Nat.cast_pos.mpr hr) (Nat.cast_pos.mpr (bdA.hs j))
   ·
    have hr0 : bc.r' j = 0 := Nat.eq_zero_of_not_pos hr
    have hP0 : P (i, j, k) = 0 := by
     rw [hP_def, bc.hAhat_zero j hr0, Matrix.mul_zero, Matrix.zero_mul]
    rw [hP0, trace_zero, zero_re, mul_zero, mul_zero]
  have hpt_le1 : ∀ p : Idx, 0 < bc.r' p.2.1 → |cTP p - cP p| ≤ 1 := by
   intro ⟨i, j, k⟩ hr
   rw [hcTP_def, hcP_def]; simp only [hr, ↓reduceIte]
   have h1 := betaFn_pos (hmu k) (div_pos (Nat.cast_pos.mpr (bdA.hr j)) (Nat.cast_pos.mpr (bdA.hs j)))
   have h2 := betaFn_lt_one (hmu k) (div_pos (Nat.cast_pos.mpr (bdA.hr j)) (Nat.cast_pos.mpr (bdA.hs j)))
   have h3 := betaFn_pos (hmu k) (div_pos (Nat.cast_pos.mpr hr) (Nat.cast_pos.mpr (bdA.hs j)))
   have h4 := betaFn_lt_one (hmu k) (div_pos (Nat.cast_pos.mpr hr) (Nat.cast_pos.mpr (bdA.hs j)))
   rw [abs_le]; constructor <;> linarith
  have hsum_abs : ∑ p : Idx, |cTP p - cP p| * ((P p).trace).re ≤ 6 * ε ^ 2 * (d : ℝ) := by
   calc
    ∑ p : Idx, |cTP p - cP p| * ((P p).trace).re
     ≤ ∑ p : Idx, (if 0 < bc.r' p.2.1 then |(bc.r' p.2.1 : ℝ) - (bdA.r p.2.1 : ℝ)| / (bc.r' p.2.1 : ℝ) else 0) *
       ((P p).trace).re := sum_le_sum fun p _ => hpt p
    _ = ∑ j : Fin bdA.t,
       (if 0 < bc.r' j then |(bc.r' j : ℝ) - (bdA.r j : ℝ)| / (bc.r' j : ℝ) else 0) *
       (∑ i : Fin bdB.t, ∑ k : Fin bdD.t, ((P (i, j, k)).trace).re) := by
       rw [sum_prod_type]
       simp_rw [sum_prod_type]
       rw [sum_comm]
       refine sum_congr rfl fun j _ => by
        rw [Finset.mul_sum]
        refine sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin bdA.t, (bdA.s j : ℝ) * |(bc.r' j : ℝ) - (bdA.r j : ℝ)| := by
       refine sum_le_sum fun j _ => ?_
       rw [hw_sum_j j]
       by_cases hr : 0 < bc.r' j
       ·
        simp only [hr, ↓reduceIte]
        have hr0 : (bc.r' j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hr)
        have : |(bc.r' j : ℝ) - (bdA.r j : ℝ)| / (bc.r' j : ℝ) * ((bc.r' j : ℝ) * (bdA.s j : ℝ)) =
          (bdA.s j : ℝ) * |(bc.r' j : ℝ) - (bdA.r j : ℝ)| := by field_simp [hr0]
        linarith
       ·
        simp only [hr, ↓reduceIte, zero_mul]
        exact mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
    _ ≤ 6 * ε ^ 2 * (d : ℝ) := bc.hA_mult
  constructor
  ·
   rw [hdiff, orthog_proj_family_hsSq P hPh hPmul]
   refine (sum_le_sum fun p _ => ?_).trans hsum_abs
   by_cases hr : 0 < bc.r' p.2.1
   ·
    have hle1 := hpt_le1 p hr
    have hsq : (cTP p - cP p) ^ 2 ≤ |cTP p - cP p| := by
     rw [← sq_abs]; nlinarith [abs_nonneg (cTP p - cP p)]
    exact mul_le_mul_of_nonneg_right hsq (hw_nn p)
   ·
    have hr0 : bc.r' p.2.1 = 0 := Nat.eq_zero_of_not_pos hr
    have hP0 : P p = 0 := by
     rw [hP_def, bc.hAhat_zero p.2.1 hr0, Matrix.mul_zero, Matrix.zero_mul]
    rw [hP0, trace_zero, zero_re, mul_zero, mul_zero]
  ·
   rw [hdiff, orthog_proj_family_trace_re]
   calc
    |∑ p : Idx, (cTP p - cP p) * ((P p).trace).re|
     ≤ ∑ p : Idx, |(cTP p - cP p) * ((P p).trace).re| := abs_sum_le_sum_abs _ _
    _ = ∑ p : Idx, |cTP p - cP p| * ((P p).trace).re :=
       sum_congr rfl fun p _ => by rw [abs_mul, abs_of_nonneg (hw_nn p)]
    _ ≤ 6 * ε ^ 2 * (d : ℝ) := hsum_abs
lemma no_drift_step {d : ℕ}
  {D A : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)} (hDA : D ≤ A)
  (bdD : BDec D) (bdA : BDec A)
  {u : Matrix (Fin d) (Fin d) ℂ} (huU : u ∈ unitaryGroup (Fin d) ℂ)
  (huD : u ∈ comm D)
  {ε : ℝ} (hε : 0 ≤ ε)
  (hinc : ∀ b ∈ conjAlg u huU A, ‖CLM b‖ ≤ 1 →
   hsSq (b - cExp A b) ≤ ε ^ 2 * (d : ℝ))
  (mu : Fin bdD.t → ℝ) (hmu : ∀ k, 0 < mu k) :
  let x := ∑ j : Fin bdA.t, ∑ k : Fin bdD.t,
   (bFn (mu k) ((bdA.r j : ℝ) / (bdA.s j : ℝ)) : ℂ) •
    (cPr bdA j * cPr bdD k)
  hsN (x - uᴴ * x * u) ≤ (15 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * sqrt (d : ℝ) ∧
  ∀ {η : ℝ}, 0 ≤ η → hsSq (x - ((1 / 2 : ℝ) : ℂ) • 1) ≤ η ^ 2 * (d : ℝ) →
   ∀ a ∈ A, ‖CLM a‖ ≤ 1 →
    hsN (a - cExp (conjAlg u huU A) a) ≤
     (sqrt (128 * (2 * η + 10 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * (1 + 2 * ε)) +
      12 * ε) * sqrt (d : ℝ) := by
 classical
 let B := conjAlg u huU A
 let bdB := conjBD bdA u huU
 have hDB : D ≤ B := by
  intro y hy
  rw [mem_conjStarSubalgebra, huD y hy, mma,
   ← star_eq_conjTranspose, mul_star_self_of_mem huU, mm1]
  exact hDA hy
 obtain ⟨bc⟩ := exists_bratteliCorrection bdB bdA hε hinc
 let x : Matrix (Fin d) (Fin d) ℂ := ∑ j : Fin bdA.t, ∑ k : Fin bdD.t,
  (bFn (mu k) ((bdA.r j : ℝ) / (bdA.s j : ℝ)) : ℂ) • (cPr bdA j * cPr bdD k)
 let y : Matrix (Fin d) (Fin d) ℂ := uᴴ * x * u
 have hxA : x ∈ A := A.sum_mem fun j _ => A.sum_mem fun k _ =>
  A.smul_mem (A.mul_mem (cPr_mem bdA j) (hDA (cPr_mem bdD k))) _
 have hyB : y ∈ B := by
  rw [mem_conjStarSubalgebra]
  have h1 : u * y * uᴴ = x := by
   dsimp only [y]
   have hUm : u * uᴴ = 1 := mul_star_self_of_mem huU
   calc
    u * (uᴴ * x * u) * uᴴ = (u * uᴴ) * x * (u * uᴴ) := by simp only [mma]
    _ = x := by rw [hUm, m1m, mm1]
  rw [h1]; exact hxA
 have hcomm_AD : ∀ j k, cPr bdA j * cPr bdD k = cPr bdD k * cPr bdA j :=
  fun j k => commutant_antitone hDA (cPr_comm bdA j) _ (cPr_mem bdD k)
 have hcomm_BD : ∀ i k, cPr bdB i * cPr bdD k = cPr bdD k * cPr bdB i :=
  fun i k => commutant_antitone hDB (cPr_comm bdB i) _ (cPr_mem bdD k)
 have hx_norm : ‖CLM x‖ ≤ 1 := by
  let Px : Fin bdA.t × Fin bdD.t → Matrix (Fin d) (Fin d) ℂ :=
   fun p => cPr bdA p.1 * cPr bdD p.2
  let cx : Fin bdA.t × Fin bdD.t → ℝ :=
   fun p => bFn (mu p.2) ((bdA.r p.1 : ℝ) / (bdA.s p.1 : ℝ))
  have hxeq : x = ∑ p : Fin bdA.t × Fin bdD.t, (cx p : ℂ) • Px p :=
   (sum_prod_type (fun p : Fin bdA.t × Fin bdD.t => (cx p : ℂ) • Px p)).symm
  rw [hxeq]
  refine orthog_proj_family_opNorm_le Px ?_ ?_ ?_ cx zero_le_one ?_
  ·
   intro ⟨j, k⟩; dsimp only [Px]
   rw [ctM, cPr_herm, cPr_herm, hcomm_AD]
  ·
   intro ⟨j₁, k₁⟩ ⟨j₂, k₂⟩; dsimp only [Px]
   calc
    (cPr bdA j₁ * cPr bdD k₁) * (cPr bdA j₂ * cPr bdD k₂)
     = (cPr bdA j₁ * cPr bdA j₂) * (cPr bdD k₁ * cPr bdD k₂) := by
       rw [mma, ← mma (cPr bdD k₁), ← hcomm_AD j₂ k₁,
        mma, mma]
    _ = if (j₁, k₁) = (j₂, k₂) then cPr bdA j₁ * cPr bdD k₁ else 0 := by
       rw [cPr_mul, cPr_mul]
       by_cases hj : j₁ = j₂ <;> by_cases hk : k₁ = k₂ <;> simp [hj, hk]
  ·
   rw [sum_prod_type]
   simp_rw [Px, ← Matrix.mul_sum, sum_cPr, mm1, sum_cPr]
  ·
   intro ⟨j, k⟩; dsimp only [cx]
   have hlam : 0 < (bdA.r j : ℝ) / (bdA.s j : ℝ) :=
    div_pos (Nat.cast_pos.mpr (bdA.hr j)) (Nat.cast_pos.mpr (bdA.hs j))
   rw [abs_of_pos (betaFn_pos (hmu k) hlam)]
   exact le_of_lt (betaFn_lt_one (hmu k) hlam)
 have hy_norm : ‖CLM y‖ ≤ 1 := by
  dsimp only [y]; rw [opNorm_conj_unitary huU]; exact hx_norm
 have hy_eq : y = ∑ i : Fin bdB.t, ∑ k : Fin bdD.t,
   (bFn (mu k) ((bdB.r i : ℝ) / (bdB.s i : ℝ)) : ℂ) •
    (cPr bdB i * cPr bdD k) := by
  dsimp only [y, x]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  have hu_ek : uᴴ * cPr bdD k * u = cPr bdD k := by
   have hUs : uᴴ * u = 1 := star_mul_self_of_mem huU
   have hcomm_u : u * cPr bdD k = cPr bdD k * u := huD _ (cPr_mem bdD k)
   calc
    uᴴ * cPr bdD k * u = uᴴ * (u * cPr bdD k) := by rw [hcomm_u, mma]
    _ = cPr bdD k := by rw [← mma, hUs, m1m]
  have hUm : u * uᴴ = 1 := mul_star_self_of_mem huU
  calc
   uᴴ * (cPr bdA i * cPr bdD k) * u
    = (uᴴ * cPr bdA i * u) * (uᴴ * cPr bdD k * u) := by
      calc
       uᴴ * (cPr bdA i * cPr bdD k) * u
        = uᴴ * cPr bdA i * (u * uᴴ) * cPr bdD k * u := by
          rw [hUm, mm1]; simp only [mma]
       _ = (uᴴ * cPr bdA i * u) * (uᴴ * cPr bdD k * u) := by simp only [mma]
   _ = cPr bdB i * cPr bdD k := by
      rw [hu_ek, ← cPr_conjBD bdA u huU i]
 have hy_tr : y.trace = x.trace := by
  dsimp only [y]
  calc
   (uᴴ * x * u).trace = (u * (uᴴ * x)).trace := trace_mul_comm _ _
   _ = x.trace := by
      rw [← mma, ← star_eq_conjTranspose,
       mul_star_self_of_mem huU, m1m]
 have hsum_πB : ∀ {α : Type} [DecidableEq α] (s : Finset α) (f : α → Matrix (Fin d) (Fin d) ℂ),
   bc.πB (∑ a ∈ s, f a) = ∑ a ∈ s, bc.πB (f a) := by
  intro α _ s f
  induction s using induction_on with
  | empty => have := bc.hπB_smul 0 0; simpa using this
  | insert a s ha ih => rw [sum_insert ha, bc.hπB_add, ih, sum_insert ha]
 have hsum_πA' : ∀ {α : Type} [DecidableEq α] (s : Finset α) (f : α → Matrix (Fin d) (Fin d) ℂ),
   bc.πA' (∑ a ∈ s, f a) = ∑ a ∈ s, bc.πA' (f a) := by
  intro α _ s f
  induction s using induction_on with
  | empty => have := bc.hπA'_smul 0 0; simpa using this
  | insert a s ha ih => rw [sum_insert ha, bc.hπA'_add, ih, sum_insert ha]
 let Idx := Fin bdB.t × Fin bdA.t × Fin bdD.t
 let P : Idx → Matrix (Fin bc.m) (Fin bc.m) ℂ :=
  fun p => bc.πB (cPr bdB p.1) * bc.πA' (cPr bdA p.2.1) * bc.πB (cPr bdD p.2.2)
 have hπB_w_comm_e : ∀ i k,
   bc.πB (cPr bdB i) * bc.πB (cPr bdD k) =
    bc.πB (cPr bdD k) * bc.πB (cPr bdB i) := by
  intro i k
  rw [← bc.hπB_mul _ _ (cPr_mem bdB i) (hDB (cPr_mem bdD k)),
   ← bc.hπB_mul _ _ (hDB (cPr_mem bdD k)) (cPr_mem bdB i), hcomm_BD]
 have hPh : ∀ p : Idx, (P p)ᴴ = P p := by
  intro ⟨i, j, k⟩; dsimp only [P]
  rw [ctM, ctM, ← bc.hπB_star, ← bc.hπA'_star,
   ← bc.hπB_star, cPr_herm, cPr_herm, cPr_herm]
  calc
   bc.πB (cPr bdD k) * (bc.πA' (cPr bdA j) * bc.πB (cPr bdB i))
    = bc.πB (cPr bdD k) * (bc.πB (cPr bdB i) * bc.πA' (cPr bdA j)) := by
      rw [bc.hπ_comm _ (cPr_mem bdB i) _ (cPr_comm bdA j)]
   _ = bc.πB (cPr bdB i) * (bc.πB (cPr bdD k) * bc.πA' (cPr bdA j)) := by
      rw [← mma, ← hπB_w_comm_e, mma]
   _ = bc.πB (cPr bdB i) * bc.πA' (cPr bdA j) * bc.πB (cPr bdD k) := by
      rw [bc.hπ_comm _ (hDB (cPr_mem bdD k)) _ (cPr_comm bdA j),
       mma]
 have hPmul : ∀ p q : Idx, P p * P q = if p = q then P p else 0 := by
  intro ⟨i₁, j₁, k₁⟩ ⟨i₂, j₂, k₂⟩; dsimp only [P]
  have hc1 := bc.hπ_comm _ (cPr_mem bdB i₂) _ (cPr_comm bdA j₁)
  have hc2 := bc.hπ_comm _ (hDB (cPr_mem bdD k₁)) _ (cPr_comm bdA j₂)
  have hrearr :
    (bc.πB (cPr bdB i₁) * bc.πA' (cPr bdA j₁) * bc.πB (cPr bdD k₁)) *
    (bc.πB (cPr bdB i₂) * bc.πA' (cPr bdA j₂) * bc.πB (cPr bdD k₂)) =
    (bc.πB (cPr bdB i₁) * bc.πB (cPr bdB i₂)) *
    (bc.πA' (cPr bdA j₁) * bc.πA' (cPr bdA j₂)) *
    (bc.πB (cPr bdD k₁) * bc.πB (cPr bdD k₂)) := by
   calc
    (bc.πB (cPr bdB i₁) * bc.πA' (cPr bdA j₁) * bc.πB (cPr bdD k₁)) *
      (bc.πB (cPr bdB i₂) * bc.πA' (cPr bdA j₂) * bc.πB (cPr bdD k₂))
     = bc.πB (cPr bdB i₁) * bc.πA' (cPr bdA j₁) *
       (bc.πB (cPr bdD k₁) * bc.πB (cPr bdB i₂)) *
       bc.πA' (cPr bdA j₂) * bc.πB (cPr bdD k₂) := by simp only [mma]
    _ = bc.πB (cPr bdB i₁) * (bc.πA' (cPr bdA j₁) * bc.πB (cPr bdB i₂)) *
       (bc.πB (cPr bdD k₁) * bc.πA' (cPr bdA j₂)) * bc.πB (cPr bdD k₂) := by
       rw [← hπB_w_comm_e i₂ k₁]; simp only [mma]
    _ = bc.πB (cPr bdB i₁) * (bc.πB (cPr bdB i₂) * bc.πA' (cPr bdA j₁)) *
       (bc.πA' (cPr bdA j₂) * bc.πB (cPr bdD k₁)) * bc.πB (cPr bdD k₂) := by
       rw [← hc1, hc2]
    _ = _ := by simp only [mma]
  rw [hrearr,
   ← bc.hπB_mul _ _ (cPr_mem bdB i₁) (cPr_mem bdB i₂),
   ← bc.hπA'_mul _ _ (cPr_comm bdA j₁) (cPr_comm bdA j₂),
   ← bc.hπB_mul _ _ (hDB (cPr_mem bdD k₁)) (hDB (cPr_mem bdD k₂)),
   cPr_mul, cPr_mul, cPr_mul]
  have hπB0 : bc.πB 0 = 0 := by simpa using bc.hπB_smul 0 0
  have hπA'0 : bc.πA' 0 = 0 := by simpa using bc.hπA'_smul 0 0
  change _ = if ((i₁, j₁, k₁) : Fin bdB.t × Fin bdA.t × Fin bdD.t) = (i₂, j₂, k₂) then _ else 0
  by_cases hi : i₁ = i₂ <;> by_cases hj : j₁ = j₂ <;> by_cases hk : k₁ = k₂ <;>
   simp [hi, hj, hk, hπB0, hπA'0]
 have hPsum : ∑ p : Idx, P p = 1 := by
  rw [sum_prod_type]
  have h1 : ∀ i : Fin bdB.t, ∑ q : Fin bdA.t × Fin bdD.t, P (i, q) = bc.πB (cPr bdB i) := by
   intro i
   rw [sum_prod_type]
   simp_rw [P, ← Matrix.mul_sum, ← hsum_πB, sum_cPr, bc.hπB_one, mm1]
   rw [← Matrix.mul_sum, ← hsum_πA', sum_cPr, bc.hπA'_one, mm1]
  simp_rw [h1, ← hsum_πB, sum_cPr, bc.hπB_one]
 have hw_nn : ∀ p : Idx, 0 ≤ ((P p).trace).re := fun p =>
  orthProj_tr_nn (hPh p) (by rw [hPmul p p, if_pos rfl])
 have hw_sum_i : ∀ i : Fin bdB.t,
   ∑ j : Fin bdA.t, ∑ k : Fin bdD.t, ((P (i, j, k)).trace).re = (bdB.r i : ℝ) * (bc.q' i : ℝ) := by
  intro i
  have h1 : ∑ j : Fin bdA.t, ∑ k : Fin bdD.t, P (i, j, k) = bc.πB (cPr bdB i) := by
   simp_rw [P, ← Matrix.mul_sum, ← hsum_πB, sum_cPr, bc.hπB_one, mm1]
   rw [← Matrix.mul_sum, ← hsum_πA', sum_cPr, bc.hπA'_one, mm1]
  have h2 : ∑ j : Fin bdA.t, ∑ k : Fin bdD.t, ((P (i, j, k)).trace).re =
    ((bc.πB (cPr bdB i)).trace).re := by
   rw [← h1, trace_sum, re_sum]
   refine sum_congr rfl fun j _ => by rw [trace_sum, re_sum]
  rw [h2, bc.hBhat_tr i]; simp [Nat.cast_mul]
 have hw_sum_j : ∀ j : Fin bdA.t,
   ∑ i : Fin bdB.t, ∑ k : Fin bdD.t, ((P (i, j, k)).trace).re = (bc.r' j : ℝ) * (bdA.s j : ℝ) := by
  intro j
  have h1 : ∑ i : Fin bdB.t, ∑ k : Fin bdD.t, P (i, j, k) = bc.πA' (cPr bdA j) := by
   simp_rw [P, ← Matrix.mul_sum, ← hsum_πB, sum_cPr, bc.hπB_one, mm1]
   rw [← Matrix.sum_mul, ← hsum_πB, sum_cPr, bc.hπB_one, m1m]
  have h2 : ∑ i : Fin bdB.t, ∑ k : Fin bdD.t, ((P (i, j, k)).trace).re =
    ((bc.πA' (cPr bdA j)).trace).re := by
   rw [← h1, trace_sum, re_sum]
   refine sum_congr rfl fun i _ => by rw [trace_sum, re_sum]
  rw [h2, bc.hAhat_tr j]; simp [Nat.cast_mul]
 let cTM : Idx → ℝ := fun p => bFn (mu p.2.2) ((bdB.r p.1 : ℝ) / (bdB.s p.1 : ℝ))
 let cM : Idx → ℝ := fun p =>
  if 0 < bc.q' p.1 then bFn (mu p.2.2) ((bdB.r p.1 : ℝ) / (bc.q' p.1 : ℝ)) else 0
 let cTP : Idx → ℝ := fun p => bFn (mu p.2.2) ((bdA.r p.2.1 : ℝ) / (bdA.s p.2.1 : ℝ))
 let cP : Idx → ℝ := fun p =>
  if 0 < bc.r' p.2.1 then bFn (mu p.2.2) ((bc.r' p.2.1 : ℝ) / (bdA.s p.2.1 : ℝ)) else 0
 let xTM : Matrix (Fin bc.m) (Fin bc.m) ℂ := ∑ p : Idx, (cTM p : ℂ) • P p
 let xM : Matrix (Fin bc.m) (Fin bc.m) ℂ := ∑ p : Idx, (cM p : ℂ) • P p
 let xTP : Matrix (Fin bc.m) (Fin bc.m) ℂ := ∑ p : Idx, (cTP p : ℂ) • P p
 let xP : Matrix (Fin bc.m) (Fin bc.m) ℂ := ∑ p : Idx, (cP p : ℂ) • P p
 have hxTM_eq : xTM = bc.πB y := by
  dsimp only [xTM, cTM]
  rw [hy_eq, hsum_πB, sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_prod_type, sum_comm, hsum_πB]
  refine sum_congr rfl fun k _ => ?_
  dsimp only
  rw [bc.hπB_smul, bc.hπB_mul _ _ (cPr_mem bdB i) (hDB (cPr_mem bdD k)),
   ← Finset.smul_sum]
  congr 1
  simp_rw [P, ← Matrix.sum_mul, ← Matrix.mul_sum, ← hsum_πA', sum_cPr, bc.hπA'_one,
   mm1]
 have hxTP_W : xTP * bc.W = bc.W * x := by
  have h1 : xTP = ∑ j : Fin bdA.t, ∑ k : Fin bdD.t,
    (bFn (mu k) ((bdA.r j : ℝ) / (bdA.s j : ℝ)) : ℂ) •
     (bc.πA' (cPr bdA j) * bc.πB (cPr bdD k)) := by
   dsimp only [xTP, cTP]
   rw [sum_prod_type]
   simp_rw [sum_prod_type]
   rw [sum_comm]
   refine sum_congr rfl fun j _ => ?_
   rw [sum_comm]
   refine sum_congr rfl fun k _ => ?_
   rw [← Finset.smul_sum]
   congr 1
   simp_rw [P, ← Matrix.sum_mul, ← hsum_πB, sum_cPr, bc.hπB_one, m1m]
  rw [h1]
  dsimp only [x]
  rw [Matrix.sum_mul, Matrix.mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Matrix.sum_mul, Matrix.mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  calc
   bc.πA' (cPr bdA j) * bc.πB (cPr bdD k) * bc.W
    = bc.πA' (cPr bdA j) * (bc.πB (cPr bdD k) * bc.W) := by simp only [mma]
   _ = bc.πA' (cPr bdA j) * (bc.W * cPr bdD k) := by
      rw [bc.hW_comm_AB _ (hDA (cPr_mem bdD k)) (hDB (cPr_mem bdD k))]
   _ = (bc.πA' (cPr bdA j) * bc.W) * cPr bdD k := by simp only [mma]
   _ = bc.W * (cPr bdA j * cPr bdD k) := by
      rw [bc.hW_comm_A' _ (cPr_comm bdA j), mma]
 obtain ⟨hxTM_M_bounds, hxTP_P_bounds⟩ :=
  no_drift_xTM_xTP_bounds bdD bdA huU mu hmu bc P (fun _ _ _ => rfl) hPh hPmul hw_nn
   hw_sum_i hw_sum_j cTM cM cTP cP (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
   xTM xM xTP xP rfl rfl rfl rfl
 have hxTP_norm : ‖CLM xTP‖ ≤ 1 := by
  refine orthog_proj_family_opNorm_le P hPh hPmul hPsum cTP zero_le_one fun ⟨i, j, k⟩ => ?_
  dsimp only [cTP]
  have hlam : (0 : ℝ) < (bdA.r j : ℝ) / (bdA.s j : ℝ) :=
   div_pos (Nat.cast_pos.mpr (bdA.hr j)) (Nat.cast_pos.mpr (bdA.hs j))
  rw [abs_of_pos (betaFn_pos (hmu k) hlam)]
  exact le_of_lt (betaFn_lt_one (hmu k) hlam)
 have hxTM_norm : ‖CLM xTM‖ ≤ 1 := by
  rw [hxTM_eq]; exact (bc.hπB_opNorm y).trans hy_norm
 have h1WW_h : (1 - bc.W * bc.Wᴴ)ᴴ = 1 - bc.W * bc.Wᴴ := by
  simp
 have h1WW_p : (1 - bc.W * bc.Wᴴ) * (1 - bc.W * bc.Wᴴ) = 1 - bc.W * bc.Wᴴ := by
  rw [msm, mms, mms, m1m, m1m,
   mm1, bc.hW_tgt]; abel
 have h1W'W_h : (1 - bc.Wᴴ * bc.W)ᴴ = 1 - bc.Wᴴ * bc.W := by
  simp
 have h1W'W_p : (1 - bc.Wᴴ * bc.W) * (1 - bc.Wᴴ * bc.W) = 1 - bc.Wᴴ * bc.W := by
  rw [msm, mms, mms, m1m, m1m,
   mm1, bc.hW_src]; abel
 have hW_hsNorm : hsN bc.W ≤ sqrt (d : ℝ) := by
  have hsq : hsSq bc.W ≤ (d : ℝ) := by
   have h1 : hsSq bc.W = ((bc.Wᴴ * bc.W).trace).re := hsSq_tr bc.W
   have h2 : ((1 - bc.Wᴴ * bc.W).trace).re = (d : ℝ) - ((bc.Wᴴ * bc.W).trace).re := by
    rw [trace_sub, sub_re, trace_one, card_fin]; simp
   have h3 : 0 ≤ ((1 - bc.Wᴴ * bc.W).trace).re := orthProj_tr_nn h1W'W_h h1W'W_p
   linarith
  exact sqrt_le_sqrt hsq
 have htr_TP_x : |(xTP.trace - x.trace).re| ≤ 6 * ε ^ 2 * (d : ℝ) := by
  have heq : xTP.trace - x.trace =
    (xTP * (1 - bc.W * bc.Wᴴ)).trace - ((1 - bc.Wᴴ * bc.W) * x).trace := by
   have hmid : (xTP * (bc.W * bc.Wᴴ)).trace = (bc.Wᴴ * bc.W * x).trace := by
    calc
     (xTP * (bc.W * bc.Wᴴ)).trace = ((xTP * bc.W) * bc.Wᴴ).trace := by rw [mma]
     _ = (bc.Wᴴ * (xTP * bc.W)).trace := trace_mul_comm _ _
     _ = (bc.Wᴴ * bc.W * x).trace := by rw [hxTP_W, mma]
   rw [mms xTP, mm1, msm (1 : Matrix (Fin d) (Fin d) ℂ),
    m1m, trace_sub, trace_sub, hmid]
   ring
  rw [heq]
  have hre1 : |((xTP * (1 - bc.W * bc.Wᴴ)).trace).re| ≤ 4 * ε ^ 2 * (d : ℝ) :=
   (Complex.abs_re_le_norm _).trans ((norm_trace_mul_proj_le xTP _ h1WW_h h1WW_p).trans
    (by nlinarith [orthProj_tr_nn h1WW_h h1WW_p, bc.hW_tgt_tr]))
  have hre2 : |(((1 - bc.Wᴴ * bc.W) * x).trace).re| ≤ 2 * ε ^ 2 * (d : ℝ) :=
   (Complex.abs_re_le_norm _).trans ((norm_trace_proj_mul_le _ x h1W'W_h h1W'W_p).trans
    (by nlinarith [orthProj_tr_nn h1W'W_h h1W'W_p, bc.hW_src_tr]))
  rw [sub_re]
  exact (abs_sub _ _).trans (by linarith)
 have htr_TM_y : |(xTM.trace - y.trace).re| ≤ (6 * ε + 6 * ε ^ 2) * (d : ℝ) := by
  have heq : xTM.trace - y.trace =
    (xTM * (1 - bc.W * bc.Wᴴ)).trace + ((bc.πB y * bc.W - bc.W * y) * bc.Wᴴ).trace -
     ((1 - bc.Wᴴ * bc.W) * y).trace := by
   have hmid : (xTM * (bc.W * bc.Wᴴ)).trace =
     ((bc.πB y * bc.W - bc.W * y) * bc.Wᴴ).trace + (bc.Wᴴ * bc.W * y).trace := by
    rw [hxTM_eq, msm, trace_sub]
    have h1 : ((bc.W * y) * bc.Wᴴ).trace = (bc.Wᴴ * bc.W * y).trace := by
     rw [trace_mul_comm, mma]
    rw [h1, mma]; ring
   rw [mms xTM, mm1, msm (1 : Matrix (Fin d) (Fin d) ℂ),
    m1m, trace_sub, trace_sub, hmid]
   ring
  rw [heq]
  have hre1 : |((xTM * (1 - bc.W * bc.Wᴴ)).trace).re| ≤ 4 * ε ^ 2 * (d : ℝ) :=
   (Complex.abs_re_le_norm _).trans ((norm_trace_mul_proj_le xTM _ h1WW_h h1WW_p).trans
    (by nlinarith [orthProj_tr_nn h1WW_h h1WW_p, bc.hW_tgt_tr]))
  have hre2 : |(((1 - bc.Wᴴ * bc.W) * y).trace).re| ≤ 2 * ε ^ 2 * (d : ℝ) :=
   (Complex.abs_re_le_norm _).trans ((norm_trace_proj_mul_le _ y h1W'W_h h1W'W_p).trans
    (by nlinarith [orthProj_tr_nn h1W'W_h h1W'W_p, bc.hW_src_tr]))
  have hre3 : |(((bc.πB y * bc.W - bc.W * y) * bc.Wᴴ).trace).re| ≤ 6 * ε * (d : ℝ) := by
   refine (Complex.abs_re_le_norm _).trans ?_
   rw [trace_mul_comm]
   calc
    ‖(bc.Wᴴ * (bc.πB y * bc.W - bc.W * y)).trace‖
     ≤ hsN bc.W * hsN (bc.πB y * bc.W - bc.W * y) := norm_trace_conjTranspose_mul_le _ _
    _ ≤ sqrt (d : ℝ) * (6 * ε * sqrt (d : ℝ)) :=
      mul_le_mul hW_hsNorm (bc.hW_approx_B y hyB hy_norm) (hsN_nn _) (sqrt_nonneg _)
    _ = 6 * ε * (sqrt (d : ℝ) * sqrt (d : ℝ)) := by ring
    _ = 6 * ε * (d : ℝ) := by rw [mul_self_sqrt (Nat.cast_nonneg d)]
  rw [sub_re, Complex.add_re]
  calc
   |((xTM * (1 - bc.W * bc.Wᴴ)).trace).re +
      (((bc.πB y * bc.W - bc.W * y) * bc.Wᴴ).trace).re -
      (((1 - bc.Wᴴ * bc.W) * y).trace).re|
    ≤ |((xTM * (1 - bc.W * bc.Wᴴ)).trace).re +
      (((bc.πB y * bc.W - bc.W * y) * bc.Wᴴ).trace).re| +
     |(((1 - bc.Wᴴ * bc.W) * y).trace).re| := abs_sub _ _
   _ ≤ |((xTM * (1 - bc.W * bc.Wᴴ)).trace).re| +
      |(((bc.πB y * bc.W - bc.W * y) * bc.Wᴴ).trace).re| +
      |(((1 - bc.Wᴴ * bc.W) * y).trace).re| := by
       have hadd := abs_add_le
        ((xTM * (1 - bc.W * bc.Wᴴ)).trace).re
        (((bc.πB y * bc.W - bc.W * y) * bc.Wᴴ).trace).re
       linarith
   _ ≤ (6 * ε + 6 * ε ^ 2) * (d : ℝ) := by linarith
 have hcM_le_cP : ∀ p : Idx, P p ≠ 0 →
   0 < bc.q' p.1 ∧ 0 < bc.r' p.2.1 ∧ 0 < cM p ∧ cM p ≤ cP p ∧ cP p < 1 := by
  intro ⟨i, j, k⟩ hne
  have hqi : 0 < bc.q' i := Nat.pos_of_ne_zero fun h0 => hne (by
   dsimp only [P]; rw [bc.hBhat_zero i h0, Matrix.zero_mul, Matrix.zero_mul])
  have hrj : 0 < bc.r' j := Nat.pos_of_ne_zero fun h0 => hne (by
   dsimp only [P]; rw [bc.hAhat_zero j h0, Matrix.mul_zero, Matrix.zero_mul])
  let i' := bc.eB.symm ⟨i, hqi⟩
  let j' := bc.eA.symm ⟨j, hrj⟩
  have hi' : (bc.eB i').1 = i := congrArg Subtype.val (bc.eB.apply_symm_apply ⟨i, hqi⟩)
  have hj' : (bc.eA j').1 = j := congrArg Subtype.val (bc.eA.apply_symm_apply ⟨j, hrj⟩)
  have hne_z : cPr bc.bdAhat j' * cPr bc.bdBhat i' ≠ 0 := by
   intro h0
   apply hne
   dsimp only [P]
   rw [bc.hπ_comm _ (cPr_mem bdB i) _ (cPr_comm bdA j)]
   rw [← hi', ← hj', ← bc.hAhat_z j', ← bc.hBhat_z i', h0, Matrix.zero_mul]
  have hscale := cell_scale_ge_one bc.hBAhat bc.bdBhat bc.bdAhat i' j' hne_z
  rw [bc.hBhat_r, bc.hBhat_s, bc.hAhat_r, bc.hAhat_s, hi', hj'] at hscale
  have hscale_R : (bdB.r i : ℝ) * (bdA.s j : ℝ) ≤ (bc.q' i : ℝ) * (bc.r' j : ℝ) := by
   exact_mod_cast hscale
  have hlam_le : (bdB.r i : ℝ) / (bc.q' i : ℝ) ≤ (bc.r' j : ℝ) / (bdA.s j : ℝ) := by
   rw [div_le_div_iff₀ (Nat.cast_pos.mpr hqi) (Nat.cast_pos.mpr (bdA.hs j))]
   linarith
  have hlam1_pos : 0 < (bdB.r i : ℝ) / (bc.q' i : ℝ) :=
   div_pos (Nat.cast_pos.mpr (bdB.hr i)) (Nat.cast_pos.mpr hqi)
  have hlam2_pos : 0 < (bc.r' j : ℝ) / (bdA.s j : ℝ) :=
   div_pos (Nat.cast_pos.mpr hrj) (Nat.cast_pos.mpr (bdA.hs j))
  exact ⟨hqi, hrj,
   by simp only [cM, hqi, ↓reduceIte]; exact betaFn_pos (hmu k) hlam1_pos,
   by simp only [cM, cP, hqi, hrj, ↓reduceIte]; exact betaFn_mono (hmu k) hlam1_pos hlam_le,
   by simp only [cP, hrj, ↓reduceIte]; exact betaFn_lt_one (hmu k) hlam2_pos⟩
 have hxP_M_sq : hsSq (xP - xM) ≤ (6 * ε + 26 * ε ^ 2) * (d : ℝ) := by
  have hdiff : xP - xM = ∑ p : Idx, ((cP p - cM p : ℝ) : ℂ) • P p := by
   dsimp only [xP, xM]
   rw [← sum_sub_distrib]
   refine sum_congr rfl fun p _ => by rw [← sub_smul, ofReal_sub]
  have hle_tr : hsSq (xP - xM) ≤ ((xP - xM).trace).re := by
   rw [hdiff, orthog_proj_family_hsSq P hPh hPmul, orthog_proj_family_trace_re]
   refine sum_le_sum fun p _ => ?_
   by_cases h0 : P p = 0
   · rw [h0, trace_zero, zero_re, mul_zero, mul_zero]
   ·
    obtain ⟨_, _, h1, h2, h3⟩ := hcM_le_cP p h0
    have hsq : (cP p - cM p) ^ 2 ≤ cP p - cM p := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq (hw_nn p)
  have htr_split : ((xP - xM).trace).re =
    -((xTP - xP).trace).re + (xTP.trace - x.trace).re -
     (xTM.trace - y.trace).re + ((xTM - xM).trace).re := by
   rw [trace_sub, trace_sub, trace_sub, hy_tr]
   simp only [sub_re]; ring
  have h1 := neg_le_abs ((xTP - xP).trace).re
  have h2 := le_abs_self (xTP.trace - x.trace).re
  have h3 := neg_le_abs (xTM.trace - y.trace).re
  have h4 := le_abs_self ((xTM - xM).trace).re
  linarith [hxTP_P_bounds.2, hxTM_M_bounds.2]
 have h1W'W_norm : hsN (1 - bc.Wᴴ * bc.W) ≤ 2 * ε * sqrt (d : ℝ) := by
  have hsq : hsSq (1 - bc.Wᴴ * bc.W) ≤ (2 * ε * sqrt (d : ℝ)) ^ 2 := by
   rw [hsSq_tr, h1W'W_h, h1W'W_p, mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg d)]
   have h0 : 0 ≤ ε ^ 2 * (d : ℝ) := mul_nonneg (sq_nonneg ε) (Nat.cast_nonneg d)
   have ht := bc.hW_src_tr
   linarith
  have hrt := sqrt_le_sqrt hsq
  rwa [sqrt_sq (by positivity)] at hrt
 have h1WW_norm : hsN (1 - bc.W * bc.Wᴴ) ≤ 2 * ε * sqrt (d : ℝ) := by
  have hsq : hsSq (1 - bc.W * bc.Wᴴ) ≤ (2 * ε * sqrt (d : ℝ)) ^ 2 := by
   rw [hsSq_tr, h1WW_h, h1WW_p, mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg d)]
   have ht := bc.hW_tgt_tr
   linarith
  have hrt := sqrt_le_sqrt hsq
  rwa [sqrt_sq (by positivity)] at hrt
 have hTM_M_norm : hsN (xTM - xM) ≤ 3 * ε * sqrt (d : ℝ) := by
  have hsq : hsSq (xTM - xM) ≤ (3 * ε * sqrt (d : ℝ)) ^ 2 := by
   rw [mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg d)]
   have h0 : 0 ≤ ε ^ 2 * (d : ℝ) := mul_nonneg (sq_nonneg ε) (Nat.cast_nonneg d)
   have hb := hxTM_M_bounds.1
   linarith
  have hrt := sqrt_le_sqrt hsq
  rwa [sqrt_sq (by positivity)] at hrt
 have hTP_P_norm : hsN (xTP - xP) ≤ 3 * ε * sqrt (d : ℝ) := by
  have hsq : hsSq (xTP - xP) ≤ (3 * ε * sqrt (d : ℝ)) ^ 2 := by
   rw [mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg d)]
   have h0 : 0 ≤ ε ^ 2 * (d : ℝ) := mul_nonneg (sq_nonneg ε) (Nat.cast_nonneg d)
   have hb := hxTP_P_bounds.1
   linarith
  have hrt := sqrt_le_sqrt hsq
  rwa [sqrt_sq (by positivity)] at hrt
 have hP_M_norm : hsN (xP - xM) ≤ sqrt (6 * ε + 26 * ε ^ 2) * sqrt (d : ℝ) := by
  have hrt := sqrt_le_sqrt hxP_M_sq
  rwa [sqrt_mul (by positivity)] at hrt
 have hW_src_conj : (bc.Wᴴᴴ * bc.Wᴴ) * (bc.Wᴴᴴ * bc.Wᴴ) = bc.Wᴴᴴ * bc.Wᴴ := by
  simpa [ctct] using bc.hW_tgt
 constructor
 ·
  have hWxy : hsN (bc.W * (x - y)) ≤
    (12 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * sqrt (d : ℝ) := by
   have hsplit : bc.W * (x - y) = (xTP - xTM) * bc.W + (bc.πB y * bc.W - bc.W * y) := by
    rw [mms, msm, hxTP_W, hxTM_eq]; abel
   have h1 : hsN ((xTP - xTM) * bc.W) ≤ hsN (xTP - xTM) :=
    hsN_piR bc.W bc.hW_tgt _
   have h2 : hsN (xTP - xTM) ≤ (6 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * sqrt (d : ℝ) := by
    have hdecomp : xTP - xTM = (xTP - xP) + (xP - xM) - (xTM - xM) := by abel
    rw [hdecomp]
    calc
     hsN ((xTP - xP) + (xP - xM) - (xTM - xM))
      ≤ hsN ((xTP - xP) + (xP - xM)) + hsN (xTM - xM) := hsN_sub _ _
     _ ≤ hsN (xTP - xP) + hsN (xP - xM) + hsN (xTM - xM) := by
        linarith [hsN_add (xTP - xP) (xP - xM)]
     _ ≤ (6 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * sqrt (d : ℝ) := by linarith
   rw [hsplit]
   calc
    hsN ((xTP - xTM) * bc.W + (bc.πB y * bc.W - bc.W * y))
     ≤ hsN ((xTP - xTM) * bc.W) + hsN (bc.πB y * bc.W - bc.W * y) := hsN_add _ _
    _ ≤ (12 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * sqrt (d : ℝ) := by
       linarith [bc.hW_approx_B y hyB hy_norm]
  have hxy_split : x - y = bc.Wᴴ * (bc.W * (x - y)) + (1 - bc.Wᴴ * bc.W) * (x - y) := by
   rw [msm, m1m, mma]; abel
  have h1 : hsN (bc.Wᴴ * (bc.W * (x - y))) ≤ hsN (bc.W * (x - y)) :=
   hsN_piL bc.Wᴴ hW_src_conj _
  have h2 : hsN ((1 - bc.Wᴴ * bc.W) * (x - y)) ≤ 3 * ε * sqrt (d : ℝ) := by
   have hxy_n : ‖CLM (x - y)‖ ≤ 2 := by
    dsimp only [CLM] at hx_norm hy_norm ⊢
    rw [map_sub]; exact (norm_sub_le _ _).trans (by linarith)
   have hsq_1 : hsN (1 - bc.Wᴴ * bc.W) ≤ (3 / 2 : ℝ) * ε * sqrt (d : ℝ) := by
    have hsq : hsSq (1 - bc.Wᴴ * bc.W) ≤ ((3 / 2 : ℝ) * ε * sqrt (d : ℝ)) ^ 2 := by
     rw [hsSq_tr, h1W'W_h, h1W'W_p, mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg d)]
     have h0 : 0 ≤ ε ^ 2 * (d : ℝ) := mul_nonneg (sq_nonneg ε) (Nat.cast_nonneg d)
     have ht := bc.hW_src_tr
     linarith
    have hrt := sqrt_le_sqrt hsq
    rwa [sqrt_sq (by positivity)] at hrt
   calc
    hsN ((1 - bc.Wᴴ * bc.W) * (x - y))
     ≤ ‖CLM (x - y)‖ * hsN (1 - bc.Wᴴ * bc.W) := hsN_mulR _ _
    _ ≤ 2 * ((3 / 2 : ℝ) * ε * sqrt (d : ℝ)) :=
      mul_le_mul hxy_n hsq_1 (hsN_nn _) zero_le_two
    _ = 3 * ε * sqrt (d : ℝ) := by ring
  change hsN (x - y) ≤ _
  rw [hxy_split]
  calc
   hsN (bc.Wᴴ * (bc.W * (x - y)) + (1 - bc.Wᴴ * bc.W) * (x - y))
    ≤ hsN (bc.Wᴴ * (bc.W * (x - y))) + hsN ((1 - bc.Wᴴ * bc.W) * (x - y)) := hsN_add _ _
   _ ≤ (15 * ε + sqrt (6 * ε + 26 * ε ^ 2)) * sqrt (d : ℝ) := by linarith
 ·
  intro η hη hx_half a ha ha_norm
  exact no_drift_partB bdD bdA huU hε mu hmu bc P (fun _ _ _ => rfl) hPh hPmul hPsum hw_nn
   hsum_πB cM cTP cP (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) x xM xTP xP rfl rfl rfl
   hxTP_W h1W'W_norm h1WW_norm hTP_P_norm hP_M_norm hcM_le_cP hη hx_half ha ha_norm
lemma uniform_near_inclusion (d : ℕ → ℕ)
  (hd : ∀ᶠ n in hyperfilter ℕ, 0 < d n)
  (B A : (n : ℕ) → StarSubalgebra ℂ (Matrix (Fin (d n)) (Fin (d n)) ℂ))
  (happrox : ∀ b : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ,
   (∀ n, b n ∈ B n) → (∀ n, ‖CLM (b n)‖ ≤ 1) →
   ∃ a : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ,
    (∀ n, a n ∈ A n) ∧
    Tendsto (fun n => hsSq (b n - a n) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)) :
  ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε (hyperfilter ℕ) (𝓝 0) ∧
   ∀ n, ∀ b ∈ B n, ‖CLM b‖ ≤ 1 → hsSq (b - cExp (A n) b) ≤ (ε n) ^ 2 * (d n : ℝ) := by
 classical
 let S (n : ℕ) : Set ℝ :=
  {r | ∃ b ∈ B n, ‖CLM b‖ ≤ 1 ∧ r = hsSq (b - cExp (A n) b) / (d n : ℝ)}
 have hSne : ∀ n, (S n).Nonempty := fun n =>
  ⟨0, 0, (B n).zero_mem, by simp [CLM], by simp [hsSq]⟩
 have hSbdd : ∀ n, BddAbove (S n) := fun n => by
  refine ⟨1, ?_⟩
  rintro r ⟨b, _, hbn, rfl⟩
  by_cases h0 : d n = 0
  ·
   have hzero : hsSq (b - cExp (A n) b) = 0 := by
    unfold hsSq
    exact sum_eq_zero fun i _ => absurd i.isLt (by omega)
   rw [hzero, zero_div]; norm_num
  ·
   have hpos : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
   rw [div_le_one hpos]
   have h1 : hsSq (b - cExp (A n) b) ≤ hsSq b := by
    have := hsSq_eq_hsSq_condExp_add (A n) b; linarith [hsSq_nonneg (cExp (A n) b)]
   have h2 := hsSq_le_card_mul_opNorm_sq b
   rw [card_fin] at h2
   have hbn2 : ‖CLM b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (CLM b)]
   nlinarith
 let δ : ℕ → ℝ := fun n => if 0 < d n then sSup (S n) else 0
 let ε : ℕ → ℝ := fun n => sqrt (δ n)
 have hδ_nn : ∀ n, 0 ≤ δ n := fun n => by
  dsimp only [δ]
  split_ifs
  · exact le_csSup (hSbdd n) ⟨0, (B n).zero_mem, by simp [CLM], by simp [hsSq]⟩
  · exact le_refl 0
 have hε_nn : ∀ n, 0 ≤ ε n := fun n => sqrt_nonneg _
 have hinc : ∀ n, ∀ b ∈ B n, ‖CLM b‖ ≤ 1 → hsSq (b - cExp (A n) b) ≤ (ε n) ^ 2 * (d n : ℝ) := by
  intro n b hb hbn
  dsimp only [ε]
  rw [sq_sqrt (hδ_nn n)]
  by_cases h0 : 0 < d n
  ·
   dsimp only [δ]; rw [if_pos h0]
   have hpos : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.mpr h0
   have hle : hsSq (b - cExp (A n) b) / (d n : ℝ) ≤ sSup (S n) :=
    le_csSup (hSbdd n) ⟨b, hb, hbn, rfl⟩
   rwa [div_le_iff₀ hpos] at hle
  ·
   have hd0 : d n = 0 := Nat.eq_zero_of_not_pos h0
   have hzero : hsSq (b - cExp (A n) b) = 0 := by
    unfold hsSq
    exact sum_eq_zero fun i _ => absurd i.isLt (by omega)
   rw [hzero, hd0]; simp
 have hb_ex : ∀ n, ∃ b : Matrix (Fin (d n)) (Fin (d n)) ℂ,
   b ∈ B n ∧ ‖CLM b‖ ≤ 1 ∧ δ n ≤ 2 * (hsSq (b - cExp (A n) b) / (d n : ℝ)) := by
  intro n
  by_cases hpos : 0 < δ n
  ·
   have hdn : 0 < d n := by
    by_contra h
    dsimp only [δ] at hpos; rw [if_neg h] at hpos; linarith
   have hlt : δ n / 2 < sSup (S n) := by
    dsimp only [δ] at hpos ⊢; rw [if_pos hdn] at hpos ⊢; linarith
   obtain ⟨r, ⟨b, hb, hbn, rfl⟩, hr⟩ := exists_lt_of_lt_csSup (hSne n) hlt
   exact ⟨b, hb, hbn, by linarith⟩
  ·
   have h0 : δ n = 0 := le_antisymm (not_lt.mp hpos) (hδ_nn n)
   exact ⟨0, (B n).zero_mem, by simp [CLM], by rw [h0]; simp [hsSq]⟩
 choose b hbB hbn hδ_le using hb_ex
 obtain ⟨a, haA, ha_tend⟩ := happrox b hbB hbn
 have hδ_tend : Tendsto δ (hyperfilter ℕ) (𝓝 0) := by
  have hupper : Tendsto (fun n => 2 * (hsSq (b n - a n) / (d n : ℝ))) (hyperfilter ℕ) (𝓝 0) := by
   simpa using ha_tend.const_mul 2
  refine squeeze_zero' (Eventually.of_forall hδ_nn) ?_ hupper
  filter_upwards [hd] with n hdn
  have hle := hsSq_sub_condExp_le (A n) (b n) (haA n)
  have hpos : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.mpr hdn
  have hdiv : hsSq (b n - cExp (A n) (b n)) / (d n : ℝ) ≤ hsSq (b n - a n) / (d n : ℝ) :=
   div_le_div_of_nonneg_right hle (le_of_lt hpos)
  linarith [hδ_le n]
 have hε_tend : Tendsto ε (hyperfilter ℕ) (𝓝 0) := by
  have := (Real.continuous_sqrt.tendsto 0).comp hδ_tend
  simpa [Function.comp_def, ε] using this
 exact ⟨ε, hε_nn, hε_tend, hinc⟩
lemma tendsto_hsSq_hsN (d : ℕ → ℕ)
  (_hd : ∀ n, 0 < d n)
  (f : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) :
  Tendsto (fun n => hsSq (f n) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) ↔
   Tendsto (fun n => hsN (f n) / sqrt (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
 constructor
 ·
  intro h
  have h1 := (Real.continuous_sqrt.tendsto 0).comp h
  simp only [Function.comp_def, Real.sqrt_zero] at h1
  refine h1.congr fun n => ?_
  rw [sqrt_div (hsSq_nonneg _), hsN]
 ·
  intro h
  have h1 : Tendsto (fun n => (hsN (f n) / sqrt (d n : ℝ)) ^ 2) (hyperfilter ℕ) (𝓝 (0 ^ 2)) :=
   h.pow 2
  rw [zero_pow two_ne_zero] at h1
  refine h1.congr fun n => ?_
  rw [div_pow, hsNorm_sq, sq_sqrt (Nat.cast_nonneg (d n))]
lemma round_unitary_to_commutant {d : ℕ}
  {D₀ : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  {A₀ : StarSubalgebra ℂ (Matrix (Fin d) (Fin d) ℂ)}
  {bdD₀ : BDec D₀} {bdA₀ : BDec A₀} {ε₀ : ℝ}
  (bc : BCData bdD₀ bdA₀ ε₀)
  (hε₀ : 0 ≤ ε₀)
  (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ unitaryGroup (Fin d) ℂ) :
  ∃ (v u' : Matrix (Fin bc.m) (Fin bc.m) ℂ),
   v ∈ unitaryGroup (Fin bc.m) ℂ ∧
   u' ∈ unitaryGroup (Fin bc.m) ℂ ∧
   u' ∈ comm bc.Bhat ∧
   hsN (v - bc.W * U * bc.Wᴴ) ≤ 4 * ε₀ * sqrt (d : ℝ) ∧
   hsN (v * bc.W - bc.W * U) ≤ 6 * ε₀ * sqrt (d : ℝ) ∧
   hsN (u' - v) ≤ 3 * hsN (v - cExp (comm bc.Bhat) v) ∧
   ∃ b ∈ D₀, ‖CLM b‖ ≤ 1 ∧
    hsN (v - cExp (comm bc.Bhat) v) ≤
     hsN (U * b - b * U) + 28 * ε₀ * sqrt (d : ℝ) := by
 classical
 have h1WW_h : (1 - bc.W * bc.Wᴴ)ᴴ = 1 - bc.W * bc.Wᴴ := by
  simp
 have h1WW_p : (1 - bc.W * bc.Wᴴ) * (1 - bc.W * bc.Wᴴ) = 1 - bc.W * bc.Wᴴ := by
  rw [msm, mms, mms, m1m, m1m,
   mm1, bc.hW_tgt]; abel
 have h1W'W_h : (1 - bc.Wᴴ * bc.W)ᴴ = 1 - bc.Wᴴ * bc.W := by
  simp
 have h1W'W_p : (1 - bc.Wᴴ * bc.W) * (1 - bc.Wᴴ * bc.W) = 1 - bc.Wᴴ * bc.W := by
  rw [msm, mms, mms, m1m, m1m,
   mm1, bc.hW_src]; abel
 have h1WW_n : hsN (1 - bc.W * bc.Wᴴ) ≤ 2 * ε₀ * sqrt (d : ℝ) := by
  have hsq : hsSq (1 - bc.W * bc.Wᴴ) ≤ (2 * ε₀ * sqrt (d : ℝ)) ^ 2 := by
   rw [hsSq_tr, h1WW_h, h1WW_p, mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg d)]
   nlinarith [bc.hW_tgt_tr]
  have hrt := sqrt_le_sqrt hsq
  rwa [sqrt_sq (by positivity)] at hrt
 have h1W'W_n : hsN (1 - bc.Wᴴ * bc.W) ≤ 2 * ε₀ * sqrt (d : ℝ) := by
  have hsq : hsSq (1 - bc.Wᴴ * bc.W) ≤ (2 * ε₀ * sqrt (d : ℝ)) ^ 2 := by
   rw [hsSq_tr, h1W'W_h, h1W'W_p, mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg d)]
   nlinarith [bc.hW_src_tr, sq_nonneg ε₀, Nat.cast_nonneg (α := ℝ) d]
  have hrt := sqrt_le_sqrt hsq
  rwa [sqrt_sq (by positivity)] at hrt
 have hW_tgt_conj : (bc.Wᴴ * bc.Wᴴᴴ) * (bc.Wᴴ * bc.Wᴴᴴ) = bc.Wᴴ * bc.Wᴴᴴ := by
  simpa [ctct] using bc.hW_src
 let M₀ : Matrix (Fin bc.m) (Fin bc.m) ℂ := bc.W * U * bc.Wᴴ
 obtain ⟨v, hvU, hv_le⟩ := exists_unitary_polar_square M₀
 have hvM₀ : hsN (v - M₀) ≤ 4 * ε₀ * sqrt (d : ℝ) := by
  have h1M₀ : 1 - M₀ᴴ * M₀ =
    (1 - bc.W * bc.Wᴴ) + bc.W * Uᴴ * (1 - bc.Wᴴ * bc.W) * U * bc.Wᴴ := by
   dsimp only [M₀]
   have hUs : Uᴴ * U = 1 := star_mul_self_of_mem hU
   rw [ctM, ctM, ctct]
   rw [mms, mm1, msm, msm]
   have h1 : bc.W * Uᴴ * U * bc.Wᴴ = bc.W * bc.Wᴴ := by
    rw [mma bc.W, hUs, mm1]
   rw [h1]; simp only [mma]; abel
  have h1M₀_n : hsN (1 - M₀ᴴ * M₀) ≤ 4 * ε₀ * sqrt (d : ℝ) := by
   rw [h1M₀]
   have h2 : hsN (bc.W * Uᴴ * (1 - bc.Wᴴ * bc.W) * U * bc.Wᴴ) ≤ hsN (1 - bc.Wᴴ * bc.W) := by
    calc
     hsN (bc.W * Uᴴ * (1 - bc.Wᴴ * bc.W) * U * bc.Wᴴ)
      ≤ hsN (bc.W * Uᴴ * (1 - bc.Wᴴ * bc.W) * U) :=
        hsN_piR bc.Wᴴ hW_tgt_conj _
     _ = hsN (bc.W * (Uᴴ * (1 - bc.Wᴴ * bc.W))) := by
        rw [hsN, hsN, hsSq_coisoR U (mul_star_self_of_mem hU), mma]
     _ ≤ hsN (Uᴴ * (1 - bc.Wᴴ * bc.W)) := hsN_piL bc.W bc.hW_src _
     _ = hsN (1 - bc.Wᴴ * bc.W) := by
        have hUm : Uᴴᴴ * Uᴴ = 1 := by
         rw [ctct, ← star_eq_conjTranspose]
         exact mul_star_self_of_mem hU
        rw [hsN, hsN, hsSq_isoL Uᴴ hUm]
   exact (hsN_add _ _).trans (by linarith)
  exact (sqrt_le_sqrt hv_le).trans h1M₀_n
 have hvW : hsN (v * bc.W - bc.W * U) ≤ 6 * ε₀ * sqrt (d : ℝ) := by
  have hsplit : v * bc.W - bc.W * U =
    (v - M₀) * bc.W - bc.W * U * (1 - bc.Wᴴ * bc.W) := by
   dsimp only [M₀]; rw [msm, mms, mm1]
   simp only [mma]; abel
  rw [hsplit]
  have h1 : hsN ((v - M₀) * bc.W) ≤ hsN (v - M₀) :=
   hsN_piR bc.W bc.hW_tgt _
  have h2 : hsN (bc.W * U * (1 - bc.Wᴴ * bc.W)) ≤ hsN (1 - bc.Wᴴ * bc.W) := by
   rw [mma]
   calc
    hsN (bc.W * (U * (1 - bc.Wᴴ * bc.W)))
     ≤ hsN (U * (1 - bc.Wᴴ * bc.W)) := hsN_piL bc.W bc.hW_src _
    _ = hsN (1 - bc.Wᴴ * bc.W) := by
       rw [hsN, hsN, hsSq_isoL U (star_mul_self_of_mem hU)]
  exact (hsN_sub _ _).trans (by linarith)
 let C : Matrix (Fin bc.m) (Fin bc.m) ℂ := cExp (comm bc.Bhat) v
 obtain ⟨u', hu'C, hu'U, hu'_le⟩ :=
  exists_unitary_polar_in_subalgebra (comm bc.Bhat) (condExp_mem (comm bc.Bhat) v)
 have hu'v : hsN (u' - v) ≤ 3 * hsN (v - C) := by
  have h1C : 1 - Cᴴ * C = (v - C)ᴴ * v + Cᴴ * (v - C) := by
   have hvs : vᴴ * v = 1 := star_mul_self_of_mem hvU
   rw [ctS, msm, mms, hvs]; abel
  have hC_n : ‖CLM C‖ ≤ 1 := (opNorm_condExp_le _ v).trans (opNorm_unitary_le' hvU)
  have h1C_n : hsN (1 - Cᴴ * C) ≤ 2 * hsN (v - C) := by
   rw [h1C]
   have h1 : hsN ((v - C)ᴴ * v) ≤ hsN (v - C) := by
    rw [hsN, hsN, hsSq_coisoR v (mul_star_self_of_mem hvU), hsSq_ct]
   have h2 : hsN (Cᴴ * (v - C)) ≤ hsN (v - C) := by
    calc
     hsN (Cᴴ * (v - C)) ≤ ‖CLM Cᴴ‖ * hsN (v - C) := hsN_mulL _ _
     _ = ‖CLM C‖ * hsN (v - C) := by rw [opNorm_conjTranspose]
     _ ≤ 1 * hsN (v - C) := mul_le_mul_of_nonneg_right hC_n (hsN_nn _)
     _ = hsN (v - C) := one_mul _
   exact (hsN_add _ _).trans (by linarith)
  have hu'C_n : hsN (u' - C) ≤ 2 * hsN (v - C) :=
   (sqrt_le_sqrt hu'_le).trans h1C_n
  have hsplit : u' - v = (u' - C) - (v - C) := by abel
  rw [hsplit]
  exact (hsN_sub _ _).trans (by linarith)
 have havg := unitary_commutator_avg_eq bc.bdBhat hvU
 have hne_hw : (univ : Finset (BHW bc.bdBhat)).Nonempty := by
  rw [Finset.univ_nonempty_iff]
  exact Fintype.card_pos_iff.mp (blockHW_card_pos bc.bdBhat)
 obtain ⟨g₀, _, hg₀_max⟩ := Finset.exists_max_image univ
  (fun g : BHW bc.bdBhat => hsSq (v * bHW bc.bdBhat g - bHW bc.bdBhat g * v))
  hne_hw
 let bhat := bHW bc.bdBhat g₀
 have hbhat_mem : bhat ∈ bc.Bhat := blockHWMat_mem bc.bdBhat g₀
 have hbhat_n : ‖CLM bhat‖ ≤ 1 := opNorm_unitary_le' (bHW_u bc.bdBhat g₀)
 obtain ⟨b, hbD₀, hbn, hbπ⟩ := bc.hBhat_lift bhat hbhat_mem
 have hbn1 : ‖CLM b‖ ≤ 1 := hbn.trans hbhat_n
 have hvC_le_comm : hsN (v - C) ≤ hsN (v * bhat - bhat * v) := by
  have hsq : hsSq (v - C) ≤ hsSq (v * bhat - bhat * v) := by
   dsimp only [C]; rw [havg]
   have hNpos : (0 : ℝ) < Fintype.card (BHW bc.bdBhat) :=
    Nat.cast_pos.mpr (blockHW_card_pos bc.bdBhat)
   have hsum_le : ∑ g : BHW bc.bdBhat,
     hsSq (v * bHW bc.bdBhat g - bHW bc.bdBhat g * v) ≤
     (Fintype.card (BHW bc.bdBhat) : ℝ) * hsSq (v * bhat - bhat * v) := by
    calc
     _ ≤ ∑ _g : BHW bc.bdBhat, hsSq (v * bhat - bhat * v) :=
        sum_le_sum fun g _ => hg₀_max g (mem_univ g)
     _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
   calc
    (2 * (Fintype.card (BHW bc.bdBhat) : ℝ))⁻¹ *
      ∑ g : BHW bc.bdBhat, hsSq (v * bHW bc.bdBhat g - bHW bc.bdBhat g * v)
     ≤ (2 * (Fintype.card (BHW bc.bdBhat) : ℝ))⁻¹ *
      ((Fintype.card (BHW bc.bdBhat) : ℝ) * hsSq (v * bhat - bhat * v)) :=
       mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = (1 / 2 : ℝ) * hsSq (v * bhat - bhat * v) := by
       field_simp [ne_of_gt hNpos]
    _ ≤ hsSq (v * bhat - bhat * v) := by linarith [hsSq_nonneg (v * bhat - bhat * v)]
  exact sqrt_le_sqrt hsq
 have hcomm_le : hsN (v * bhat - bhat * v) ≤ hsN (U * b - b * U) + 28 * ε₀ * sqrt (d : ℝ) := by
  have hsplit1 : v * bhat - bhat * v =
    (v * bhat - bhat * v) * bc.W * bc.Wᴴ + (v * bhat - bhat * v) * (1 - bc.W * bc.Wᴴ) := by
   rw [mms, mm1, mma]; abel
  have hsplit2 : (v * bhat - bhat * v) * bc.W =
    v * (bc.πB b * bc.W - bc.W * b) + (v * bc.W - bc.W * U) * b + bc.W * (U * b - b * U) -
    (bc.πB b * bc.W - bc.W * b) * U - bhat * (v * bc.W - bc.W * U) := by
   rw [hbπ, msm, mms, msm, mms,
    msm, mms]
   simp only [mma]; abel
  have hpart2 : hsN ((v * bhat - bhat * v) * bc.W) ≤
    hsN (U * b - b * U) + 24 * ε₀ * sqrt (d : ℝ) := by
   rw [hsplit2]
   have ha1 : hsN (v * (bc.πB b * bc.W - bc.W * b)) ≤ 6 * ε₀ * sqrt (d : ℝ) := by
    rw [hsN, hsSq_isoL v (star_mul_self_of_mem hvU)]
    exact bc.hW_approx_B b hbD₀ hbn1
   have ha2 : hsN ((v * bc.W - bc.W * U) * b) ≤ 6 * ε₀ * sqrt (d : ℝ) :=
    (hsN_mulR _ b).trans (by nlinarith [hvW, hsN_nn (v * bc.W - bc.W * U)])
   have ha3 : hsN (bc.W * (U * b - b * U)) ≤ hsN (U * b - b * U) :=
    hsN_piL bc.W bc.hW_src _
   have ha4 : hsN ((bc.πB b * bc.W - bc.W * b) * U) ≤ 6 * ε₀ * sqrt (d : ℝ) := by
    rw [hsN, hsSq_coisoR U (mul_star_self_of_mem hU)]
    exact bc.hW_approx_B b hbD₀ hbn1
   have ha5 : hsN (bhat * (v * bc.W - bc.W * U)) ≤ 6 * ε₀ * sqrt (d : ℝ) :=
    (hsN_mulL bhat _).trans (by nlinarith [hvW, hsN_nn (v * bc.W - bc.W * U)])
   have ht1 := hsN_sub
    (v * (bc.πB b * bc.W - bc.W * b) + (v * bc.W - bc.W * U) * b + bc.W * (U * b - b * U) -
     (bc.πB b * bc.W - bc.W * b) * U)
    (bhat * (v * bc.W - bc.W * U))
   have ht2 := hsN_sub
    (v * (bc.πB b * bc.W - bc.W * b) + (v * bc.W - bc.W * U) * b + bc.W * (U * b - b * U))
    ((bc.πB b * bc.W - bc.W * b) * U)
   have ht3 := hsN_add
    (v * (bc.πB b * bc.W - bc.W * b) + (v * bc.W - bc.W * U) * b)
    (bc.W * (U * b - b * U))
   have ht4 := hsN_add (v * (bc.πB b * bc.W - bc.W * b)) ((v * bc.W - bc.W * U) * b)
   linarith
  have hpart1 : hsN ((v * bhat - bhat * v) * (1 - bc.W * bc.Wᴴ)) ≤ 4 * ε₀ * sqrt (d : ℝ) := by
   have hclm : ‖CLM (v * bhat - bhat * v)‖ ≤ 2 := by
    dsimp only [CLM] at hbhat_n ⊢
    rw [map_sub]
    have h1 : ‖CLM (v * bhat)‖ ≤ 1 :=
     (opNorm_mul_le' v bhat).trans (by nlinarith [opNorm_unitary_le' hvU, norm_nonneg (CLM bhat)])
    have h2 : ‖CLM (bhat * v)‖ ≤ 1 :=
     (opNorm_mul_le' bhat v).trans (by nlinarith [opNorm_unitary_le' hvU, norm_nonneg (CLM v)])
    exact (norm_sub_le _ _).trans (by linarith)
   exact (hsN_mulL _ _).trans (by nlinarith [h1WW_n, hsN_nn (1 - bc.W * bc.Wᴴ)])
  rw [hsplit1]
  have hW' := hsN_piR bc.Wᴴ hW_tgt_conj ((v * bhat - bhat * v) * bc.W)
  exact (hsN_add _ _).trans (by linarith)
 exact ⟨v, u', hvU, hu'U, hu'C, hvM₀, hvW, hu'v, b, hbD₀, hbn1, hvC_le_comm.trans hcomm_le⟩
lemma oma_round_tendsto
  {d : ℕ → ℕ} (hd : ∀ n, 0 < d n) {ι : Type} [Fintype ι] (s : ι → Bool)
  (u : ι → (n : ℕ) → unitaryGroup (Fin (d n)) ℂ)
  {D₀ A₀ : (n : ℕ) → StarSubalgebra ℂ (Matrix (Fin (d n)) (Fin (d n)) ℂ)}
  (hD₀ : ∀ (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ),
   (∃ C : ℝ, ∀ n, ‖CLM (y n)‖ ≤ C) →
   (((∃ C : ℝ, ∀ n, ‖CLM (y n)‖ ≤ C) ∧ ∀ a, (true || s a) = true →
    Tendsto (fun n => hsSq ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
     y n * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)) ↔
    ∃ (a : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ), (∃ C : ℝ, ∀ n, ‖CLM (a n)‖ ≤ C) ∧ (∀ n, a n ∈ D₀ n) ∧
     Tendsto (fun n => hsSq (y n - a n) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)))
  {bdD₀ : (n : ℕ) → BDec (D₀ n)} {bdA₀ : (n : ℕ) → BDec (A₀ n)}
  {ε₀ : ℕ → ℝ} (hε₀_nn : ∀ n, 0 ≤ ε₀ n) (hε₀_tend : Tendsto ε₀ (hyperfilter ℕ) (𝓝 0))
  (bc : (n : ℕ) → BCData (bdD₀ n) (bdA₀ n) (ε₀ n)) :
  ∃ (u' : ι → (n : ℕ) → Matrix (Fin (bc n).m) (Fin (bc n).m) ℂ),
   (∀ a n, u' a n ∈ unitaryGroup (Fin (bc n).m) ℂ) ∧
   (∀ a n, u' a n ∈ comm (bc n).Bhat) ∧
   (∀ a, Tendsto (fun n => hsN (u' a n - (bc n).W * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (bc n).Wᴴ) /
    sqrt (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)) ∧
   (∀ a, Tendsto (fun n => hsN (u' a n * (bc n).W - (bc n).W * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) /
    sqrt (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)) := by
 classical
 let U (a : ι) (n : ℕ) : Matrix (Fin (d n)) (Fin (d n)) ℂ := (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)
 have h1W'W_n : ∀ n, hsN (1 - (bc n).Wᴴ * (bc n).W) ≤ 2 * ε₀ n * sqrt (d n : ℝ) := by
  intro n
  have h1h : (1 - (bc n).Wᴴ * (bc n).W)ᴴ = 1 - (bc n).Wᴴ * (bc n).W := by
   simp
  have h1p : (1 - (bc n).Wᴴ * (bc n).W) * (1 - (bc n).Wᴴ * (bc n).W) = 1 - (bc n).Wᴴ * (bc n).W := by
   rw [msm, mms, mms, m1m, m1m,
    mm1, (bc n).hW_src]; abel
  have hsq : hsSq (1 - (bc n).Wᴴ * (bc n).W) ≤ (2 * ε₀ n * sqrt (d n : ℝ)) ^ 2 := by
   rw [hsSq_tr, h1h, h1p, mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg (d n))]
   have h0 : 0 ≤ ε₀ n ^ 2 * (d n : ℝ) := mul_nonneg (sq_nonneg (ε₀ n)) (Nat.cast_nonneg (d n))
   have ht := (bc n).hW_src_tr; linarith
  have hrt := sqrt_le_sqrt hsq
  rwa [sqrt_sq (by have := hε₀_nn n; positivity)] at hrt
 have hround : ∀ (a : ι) (n : ℕ), ∃ (v u' : Matrix (Fin (bc n).m) (Fin (bc n).m) ℂ),
   v ∈ unitaryGroup (Fin (bc n).m) ℂ ∧
   u' ∈ unitaryGroup (Fin (bc n).m) ℂ ∧
   u' ∈ comm (bc n).Bhat ∧
   hsN (v - (bc n).W * U a n * (bc n).Wᴴ) ≤ 4 * ε₀ n * sqrt (d n : ℝ) ∧
   hsN (v * (bc n).W - (bc n).W * U a n) ≤ 6 * ε₀ n * sqrt (d n : ℝ) ∧
   hsN (u' - v) ≤ 3 * hsN (v - cExp (comm (bc n).Bhat) v) ∧
   ∃ b ∈ D₀ n, ‖CLM b‖ ≤ 1 ∧
    hsN (v - cExp (comm (bc n).Bhat) v) ≤
     hsN (U a n * b - b * U a n) + 28 * ε₀ n * sqrt (d n : ℝ) :=
  fun a n => round_unitary_to_commutant (bc n) (hε₀_nn n) (U a n) (u a n).2
 choose v u' _ hu'U hu'D hvM₀ _ hu'v hb_ex using hround
 have hu'_M₀_tend : ∀ a : ι,
   Tendsto (fun n => hsN (u' a n - (bc n).W * U a n * (bc n).Wᴴ) / sqrt (d n : ℝ))
    (hyperfilter ℕ) (𝓝 0) := by
  intro a
  choose b hbD₀ hbn hb_le using hb_ex a
  have hKb := (hD₀ b ⟨1, hbn⟩).mpr ⟨b, ⟨1, hbn⟩, hbD₀, by
   have h0 : ∀ n, hsSq (b n - b n) / (d n : ℝ) = 0 := fun n => by
    rw [sub_self]; simp [hsSq]
   simp_rw [h0]; exact tendsto_const_nhds⟩
  have hcomm_n : Tendsto (fun n => hsN (U a n * b n - b n * U a n) / sqrt (d n : ℝ))
    (hyperfilter ℕ) (𝓝 0) := (tendsto_hsSq_hsN d hd _).mp (hKb.2 a rfl)
  have hupper : Tendsto (fun n => 3 * (hsN (U a n * b n - b n * U a n) / sqrt (d n : ℝ)) +
    88 * ε₀ n) (hyperfilter ℕ) (𝓝 0) := by
   simpa using (hcomm_n.const_mul 3).add (hε₀_tend.const_mul 88)
  refine squeeze_zero (fun n => div_nonneg (hsN_nn _) (sqrt_nonneg _)) (fun n => ?_) hupper
  have hrt_pos : (0 : ℝ) < sqrt (d n : ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr (hd n))
  rw [div_le_iff₀ hrt_pos]
  have htri : hsN (u' a n - (bc n).W * U a n * (bc n).Wᴴ) ≤
    hsN (u' a n - v a n) + hsN (v a n - (bc n).W * U a n * (bc n).Wᴴ) := by
   have : u' a n - (bc n).W * U a n * (bc n).Wᴴ =
     (u' a n - v a n) + (v a n - (bc n).W * U a n * (bc n).Wᴴ) := by abel
   rw [this]; exact hsN_add _ _
  have hstep1 := hu'v a n; have hstep2 := hb_le n; have hstep3 := hvM₀ a n
  have hmul : (3 * (hsN (U a n * b n - b n * U a n) / sqrt (d n : ℝ)) + 88 * ε₀ n) *
    sqrt (d n : ℝ) =
    3 * hsN (U a n * b n - b n * U a n) + 88 * ε₀ n * sqrt (d n : ℝ) := by
   field_simp [ne_of_gt hrt_pos]
  rw [hmul]; linarith
 have hu'_W_tend : ∀ a : ι,
   Tendsto (fun n => hsN (u' a n * (bc n).W - (bc n).W * U a n) / sqrt (d n : ℝ))
    (hyperfilter ℕ) (𝓝 0) := by
  intro a
  have hupper : Tendsto (fun n => hsN (u' a n - (bc n).W * U a n * (bc n).Wᴴ) / sqrt (d n : ℝ) +
    2 * ε₀ n) (hyperfilter ℕ) (𝓝 0) := by
   simpa using (hu'_M₀_tend a).add (hε₀_tend.const_mul 2)
  refine squeeze_zero (fun n => div_nonneg (hsN_nn _) (sqrt_nonneg _)) (fun n => ?_) hupper
  have hrt_pos : (0 : ℝ) < sqrt (d n : ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr (hd n))
  rw [div_le_iff₀ hrt_pos]
  have hsplit : u' a n * (bc n).W - (bc n).W * U a n =
    (u' a n - (bc n).W * U a n * (bc n).Wᴴ) * (bc n).W -
     (bc n).W * U a n * (1 - (bc n).Wᴴ * (bc n).W) := by
   simp only [msm, mms, mm1, mma]; abel
  have h1 : hsN ((u' a n - (bc n).W * U a n * (bc n).Wᴴ) * (bc n).W) ≤
    hsN (u' a n - (bc n).W * U a n * (bc n).Wᴴ) :=
   hsN_piR (bc n).W (bc n).hW_tgt _
  have h2 : hsN ((bc n).W * U a n * (1 - (bc n).Wᴴ * (bc n).W)) ≤
    hsN (1 - (bc n).Wᴴ * (bc n).W) := by
   rw [mma]
   calc
    hsN ((bc n).W * (U a n * (1 - (bc n).Wᴴ * (bc n).W)))
     ≤ hsN (U a n * (1 - (bc n).Wᴴ * (bc n).W)) :=
       hsN_piL (bc n).W (bc n).hW_src _
    _ = hsN (1 - (bc n).Wᴴ * (bc n).W) := by
       rw [hsN, hsN, hsSq_isoL (U a n) (star_mul_self_of_mem (u a n).2)]
  rw [hsplit]
  have hmul : (hsN (u' a n - (bc n).W * U a n * (bc n).Wᴴ) / sqrt (d n : ℝ) + 2 * ε₀ n) *
    sqrt (d n : ℝ) =
    hsN (u' a n - (bc n).W * U a n * (bc n).Wᴴ) + 2 * ε₀ n * sqrt (d n : ℝ) := by
   field_simp [ne_of_gt hrt_pos]
  rw [hmul]
  exact (hsN_sub _ _).trans (by linarith [h1W'W_n n])
 exact ⟨u', hu'U, hu'D, hu'_M₀_tend, hu'_W_tend⟩
lemma oma_conj_near_inclusion
  {d : ℕ → ℕ} (hd : ∀ n, 0 < d n) {ι : Type} [Fintype ι] (s : ι → Bool)
  (u : ι → (n : ℕ) → unitaryGroup (Fin (d n)) ℂ)
  {D₀ A₀ : (n : ℕ) → StarSubalgebra ℂ (Matrix (Fin (d n)) (Fin (d n)) ℂ)}
  (hA₀ : ∀ (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ),
   (∃ C : ℝ, ∀ n, ‖CLM (y n)‖ ≤ C) →
   (((∃ C : ℝ, ∀ n, ‖CLM (y n)‖ ≤ C) ∧ ∀ a, (false || s a) = true →
    Tendsto (fun n => hsSq ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
     y n * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)) ↔
    ∃ (a : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ), (∃ C : ℝ, ∀ n, ‖CLM (a n)‖ ≤ C) ∧ (∀ n, a n ∈ A₀ n) ∧
     Tendsto (fun n => hsSq (y n - a n) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)))
  (hconj : ∀ a, s a = false → ∀ (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ),
   ((∃ C : ℝ, ∀ n, ‖CLM (y n)‖ ≤ C) ∧ ∀ a', (false || s a') = true →
    Tendsto (fun n => hsSq ((u a' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
     y n * (u a' n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)) →
   ((∃ C : ℝ, ∀ n, ‖CLM (star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n *
    (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ))‖ ≤ C) ∧ ∀ a', (false || s a') = true →
    Tendsto (fun n => hsSq ((u a' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) *
     (star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) -
     (star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) *
     (u a' n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)))
  {bdD₀ : (n : ℕ) → BDec (D₀ n)} {bdA₀ : (n : ℕ) → BDec (A₀ n)} {ε₀ : ℕ → ℝ}
  (bc : (n : ℕ) → BCData (bdD₀ n) (bdA₀ n) (ε₀ n))
  (hm_bounds : ∀ᶠ n in hyperfilter ℕ, (1 / 2 : ℝ) * (d n : ℝ) ≤ ((bc n).m : ℝ) ∧ ((bc n).m : ℝ) ≤ 2 * (d n : ℝ))
  (hm_pos : ∀ᶠ n in hyperfilter ℕ, 0 < (bc n).m)
  (u' : (n : ℕ) → Matrix (Fin (bc n).m) (Fin (bc n).m) ℂ)
  (hu'U : ∀ n, u' n ∈ unitaryGroup (Fin (bc n).m) ℂ)
  (a : ι) (ha : s a = false)
  (hu'_M₀_tend : Tendsto (fun n => hsN (u' n - (bc n).W * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (bc n).Wᴴ) /
   sqrt (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)) :
  ∃ εa : ℕ → ℝ, (∀ n, 0 ≤ εa n) ∧ Tendsto εa (hyperfilter ℕ) (𝓝 0) ∧
   ∀ n, ∀ b ∈ conjAlg (u' n) (hu'U n) (bc n).Ahat, ‖CLM b‖ ≤ 1 →
    hsSq (b - cExp (bc n).Ahat b) ≤ εa n ^ 2 * ((bc n).m : ℝ) := by
 classical
 let U (n : ℕ) : Matrix (Fin (d n)) (Fin (d n)) ℂ := (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)
 have hW_src_conj : ∀ n, ((bc n).Wᴴᴴ * (bc n).Wᴴ) * ((bc n).Wᴴᴴ * (bc n).Wᴴ) = (bc n).Wᴴᴴ * (bc n).Wᴴ :=
  fun n => by simpa [ctct] using (bc n).hW_tgt
 have hW_tgt_conj : ∀ n, ((bc n).Wᴴ * (bc n).Wᴴᴴ) * ((bc n).Wᴴ * (bc n).Wᴴᴴ) = (bc n).Wᴴ * (bc n).Wᴴᴴ :=
  fun n => by simpa [ctct] using (bc n).hW_src
 refine uniform_near_inclusion (fun n => (bc n).m) hm_pos
  (fun n => conjAlg (u' n) (hu'U n) (bc n).Ahat) (fun n => (bc n).Ahat) ?_
 intro b hb hbn
 let a1 (n : ℕ) := u' n * b n * (u' n)ᴴ
 have ha1_mem : ∀ n, a1 n ∈ (bc n).Ahat := fun n => hb n
 have ha1_n : ∀ n, ‖CLM (a1 n)‖ ≤ 1 := fun n => by
  dsimp only [a1]
  have h2 := opNorm_conj_unitary (Unitary.star_mem (hu'U n)) (b n)
  have h1 : ‖CLM (u' n * b n * (u' n)ᴴ)‖ = ‖CLM (b n)‖ := by
   simpa [star_eq_conjTranspose, ctct] using h2
  rw [h1]; exact hbn n
 let y (n : ℕ) := (bc n).Wᴴ * a1 n * (bc n).W
 have hyA₀ : ∀ n, y n ∈ A₀ n := fun n => (bc n).hW_conj_Ahat (a1 n) (ha1_mem n)
 have hyn : ∀ n, ‖CLM (y n)‖ ≤ 1 := fun n => by
  dsimp only [y]
  have h1 := opN_conjPI (bc n).Wᴴ (hW_src_conj n) (a1 n)
  simp only [ctct] at h1
  exact h1.trans (ha1_n n)
 have hKy := (hA₀ y ⟨1, hyn⟩).mpr ⟨y, ⟨1, hyn⟩, hyA₀, by
  have h0 : ∀ n, hsSq (y n - y n) / (d n : ℝ) = 0 := fun n => by rw [sub_self]; simp [hsSq]
  simp_rw [h0]; exact tendsto_const_nhds⟩
 have hKconj := hconj a ha y hKy
 obtain ⟨a0, _, ha0_mem, ha0_tend⟩ := (hA₀ _ hKconj.1).mp hKconj
 let a2 (n : ℕ) := (bc n).W * a0 n * (bc n).Wᴴ
 refine ⟨a2, fun n => (bc n).hW_conj_A (a0 n) (ha0_mem n), ?_⟩
 have ha0_n_tend : Tendsto (fun n => hsN ((U n)ᴴ * y n * U n - a0 n) / sqrt (d n : ℝ))
   (hyperfilter ℕ) (𝓝 0) :=
  (tendsto_hsSq_hsN d hd _).mp ha0_tend
 have hdiff_d : Tendsto (fun n => hsN (b n - a2 n) / sqrt (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
  have hupper : Tendsto (fun n =>
    2 * (hsN (u' n - (bc n).W * U n * (bc n).Wᴴ) / sqrt (d n : ℝ)) +
    hsN ((U n)ᴴ * y n * U n - a0 n) / sqrt (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
   simpa using (hu'_M₀_tend.const_mul 2).add ha0_n_tend
  refine squeeze_zero (fun n => div_nonneg (hsN_nn _) (sqrt_nonneg _)) (fun n => ?_) hupper
  have hrt_pos : (0 : ℝ) < sqrt (d n : ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr (hd n))
  rw [div_le_iff₀ hrt_pos]
  let M₀ := (bc n).W * U n * (bc n).Wᴴ
  have hb_eq : b n = (u' n)ᴴ * a1 n * u' n := by
   dsimp only [a1]
   have hUs : (u' n)ᴴ * u' n = 1 := star_mul_self_of_mem (hu'U n)
   calc
    b n = ((u' n)ᴴ * u' n) * b n * ((u' n)ᴴ * u' n) := by rw [hUs, m1m, mm1]
    _ = (u' n)ᴴ * (u' n * b n * (u' n)ᴴ) * u' n := by simp only [mma]
  have hM₀_conj : M₀ᴴ * a1 n * M₀ = (bc n).W * ((U n)ᴴ * y n * U n) * (bc n).Wᴴ := by
   dsimp only [M₀, y]
   simp only [ctM, ctct, mma]
  have hsplit : b n - a2 n =
    ((u' n)ᴴ - M₀ᴴ) * a1 n * u' n + M₀ᴴ * a1 n * (u' n - M₀) +
     (bc n).W * ((U n)ᴴ * y n * U n - a0 n) * (bc n).Wᴴ := by
   dsimp only [a2]
   rw [hb_eq]
   simp only [msm, mms]
   rw [← hM₀_conj]; abel
  have hM₀_op : ‖CLM M₀‖ ≤ 1 :=
   (opN_conjPI (bc n).W (bc n).hW_src _).trans (opNorm_unitary_le' (u a n).2)
  have ht1 : hsN (((u' n)ᴴ - M₀ᴴ) * a1 n * u' n) ≤ hsN (u' n - M₀) := by
   have h0 : hsN (((u' n)ᴴ - M₀ᴴ) * a1 n * u' n) = hsN (((u' n)ᴴ - M₀ᴴ) * a1 n) := by
    rw [hsN, hsN, hsSq_coisoR (u' n) (mul_star_self_of_mem (hu'U n))]
   rw [h0]
   have h1 : hsN (((u' n)ᴴ - M₀ᴴ) * a1 n) ≤ hsN ((u' n)ᴴ - M₀ᴴ) :=
    (hsN_mulR _ (a1 n)).trans (by nlinarith [ha1_n n, hsN_nn ((u' n)ᴴ - M₀ᴴ)])
   have h2 : hsN ((u' n)ᴴ - M₀ᴴ) = hsN (u' n - M₀) := by
    rw [← ctS, hsN_ct]
   exact h1.trans_eq h2
  have ht2 : hsN (M₀ᴴ * a1 n * (u' n - M₀)) ≤ hsN (u' n - M₀) := by
   rw [mma]
   calc
    hsN (M₀ᴴ * (a1 n * (u' n - M₀)))
     ≤ ‖CLM M₀ᴴ‖ * hsN (a1 n * (u' n - M₀)) := hsN_mulL _ _
    _ ≤ 1 * (1 * hsN (u' n - M₀)) := by
       rw [opNorm_conjTranspose]
       exact mul_le_mul hM₀_op
        ((hsN_mulL _ _).trans (mul_le_mul_of_nonneg_right (ha1_n n) (hsN_nn _)))
        (hsN_nn _) zero_le_one
    _ = hsN (u' n - M₀) := by ring
  have ht3 : hsN ((bc n).W * ((U n)ᴴ * y n * U n - a0 n) * (bc n).Wᴴ) ≤
    hsN ((U n)ᴴ * y n * U n - a0 n) :=
   (hsN_piR (bc n).Wᴴ (hW_tgt_conj n) _).trans
    (hsN_piL (bc n).W (bc n).hW_src _)
  rw [hsplit]
  have htri1 := hsN_add (((u' n)ᴴ - M₀ᴴ) * a1 n * u' n + M₀ᴴ * a1 n * (u' n - M₀))
   ((bc n).W * ((U n)ᴴ * y n * U n - a0 n) * (bc n).Wᴴ)
  have htri2 := hsN_add (((u' n)ᴴ - M₀ᴴ) * a1 n * u' n) (M₀ᴴ * a1 n * (u' n - M₀))
  have hmul : (2 * (hsN (u' n - M₀) / sqrt (d n : ℝ)) +
    hsN ((U n)ᴴ * y n * U n - a0 n) / sqrt (d n : ℝ)) * sqrt (d n : ℝ) =
    2 * hsN (u' n - M₀) + hsN ((U n)ᴴ * y n * U n - a0 n) := by
   field_simp [ne_of_gt hrt_pos]
  rw [hmul]; linarith
 have hdiff_d_sq : Tendsto (fun n => hsSq (b n - a2 n) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
  have hsq : Tendsto (fun n => (hsN (b n - a2 n) / sqrt (d n : ℝ)) ^ 2) (hyperfilter ℕ) (𝓝 0) := by
   simpa using hdiff_d.pow 2
  refine hsq.congr fun n => ?_
  rw [div_pow, hsN, sq_sqrt (hsSq_nonneg _), sq_sqrt (Nat.cast_nonneg _)]
 have hupper : Tendsto (fun n => 2 * (hsSq (b n - a2 n) / (d n : ℝ))) (hyperfilter ℕ) (𝓝 0) := by
  simpa using hdiff_d_sq.const_mul 2
 refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg (hsSq_nonneg _) (Nat.cast_nonneg _))
  ?_ hupper
 filter_upwards [hm_bounds] with n ⟨hlo, _⟩
 have hdpos : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.mpr (hd n)
 have hmpos : (0 : ℝ) < ((bc n).m : ℝ) := by linarith
 rw [div_le_iff₀ hmpos]
 have h1 : 2 * (hsSq (b n - a2 n) / (d n : ℝ)) * ((bc n).m : ℝ) =
   hsSq (b n - a2 n) * ((2 * ((bc n).m : ℝ)) / (d n : ℝ)) := by ring
 rw [h1]
 have hge1 : 1 ≤ (2 * ((bc n).m : ℝ)) / (d n : ℝ) := by rw [le_div_iff₀ hdpos]; linarith
 nlinarith [hsSq_nonneg (b n - a2 n)]
lemma oma_median_limit
  {d : ℕ → ℕ} (hd : ∀ n, 0 < d n) {ι : Type} [Fintype ι] (s : ι → Bool)
  (u : ι → (n : ℕ) → unitaryGroup (Fin (d n)) ℂ)
  {D₀ A₀ : (n : ℕ) → StarSubalgebra ℂ (Matrix (Fin (d n)) (Fin (d n)) ℂ)}
  (hA₀ : ∀ (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ),
   (∃ C : ℝ, ∀ n, ‖CLM (y n)‖ ≤ C) →
   (((∃ C : ℝ, ∀ n, ‖CLM (y n)‖ ≤ C) ∧ ∀ a, (false || s a) = true →
    Tendsto (fun n => hsSq ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
     y n * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)) ↔
    ∃ (a : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ), (∃ C : ℝ, ∀ n, ‖CLM (a n)‖ ≤ C) ∧ (∀ n, a n ∈ A₀ n) ∧
     Tendsto (fun n => hsSq (y n - a n) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)))
  (hD₀ : ∀ (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ),
   (∃ C : ℝ, ∀ n, ‖CLM (y n)‖ ≤ C) →
   (((∃ C : ℝ, ∀ n, ‖CLM (y n)‖ ≤ C) ∧ ∀ a, (true || s a) = true →
    Tendsto (fun n => hsSq ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
     y n * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)) ↔
    ∃ (a : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ), (∃ C : ℝ, ∀ n, ‖CLM (a n)‖ ≤ C) ∧ (∀ n, a n ∈ D₀ n) ∧
     Tendsto (fun n => hsSq (y n - a n) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)))
  {bdD₀ : (n : ℕ) → BDec (D₀ n)} {bdA₀ : (n : ℕ) → BDec (A₀ n)}
  {ε₀ : ℕ → ℝ} (hε₀_nn : ∀ n, 0 ≤ ε₀ n) (hε₀_tend : Tendsto ε₀ (hyperfilter ℕ) (𝓝 0))
  (bc : (n : ℕ) → BCData (bdD₀ n) (bdA₀ n) (ε₀ n))
  (hm_bounds : ∀ᶠ n in hyperfilter ℕ, (1 / 2 : ℝ) * (d n : ℝ) ≤ ((bc n).m : ℝ) ∧ ((bc n).m : ℝ) ≤ 2 * (d n : ℝ))
  (hm_pos : ∀ᶠ n in hyperfilter ℕ, 0 < (bc n).m)
  (u' : ι → (n : ℕ) → Matrix (Fin (bc n).m) (Fin (bc n).m) ℂ)
  (hu'U : ∀ a n, u' a n ∈ unitaryGroup (Fin (bc n).m) ℂ)
  (hu'D : ∀ a n, u' a n ∈ comm (bc n).Bhat)
  (hu'_W_tend : ∀ a, Tendsto (fun n => hsN (u' a n * (bc n).W -
   (bc n).W * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) / sqrt (d n : ℝ)) (hyperfilter ℕ) (𝓝 0))
  (hconj_inc : ∀ a, s a = false →
   ∃ εa : ℕ → ℝ, (∀ n, 0 ≤ εa n) ∧ Tendsto εa (hyperfilter ℕ) (𝓝 0) ∧
    ∀ n, ∀ b ∈ conjAlg (u' a n) (hu'U a n) (bc n).Ahat, ‖CLM b‖ ≤ 1 →
     hsSq (b - cExp (bc n).Ahat b) ≤ εa n ^ 2 * ((bc n).m : ℝ)) :
  ∃ (mu : (n : ℕ) → Fin (bc n).bdBhat.t → ℝ) (η : ℕ → ℝ),
   (∀ n k, 0 < mu n k) ∧ (∀ n, 0 ≤ η n) ∧ Tendsto η (hyperfilter ℕ) (𝓝 0) ∧
   ∀ n, hsSq ((∑ j : Fin (bc n).bdAhat.t, ∑ k : Fin (bc n).bdBhat.t,
    (bFn (mu n k) (((bc n).bdAhat.r j : ℝ) / ((bc n).bdAhat.s j : ℝ)) : ℂ) •
     (cPr (bc n).bdAhat j * cPr (bc n).bdBhat k)) -
    ((1 / 2 : ℝ) : ℂ) • 1) ≤ (η n) ^ 2 * ((bc n).m : ℝ) := by
 classical
 let U (a : ι) (n : ℕ) : Matrix (Fin (d n)) (Fin (d n)) ℂ := (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)
 have hW_src_conj : ∀ n, ((bc n).Wᴴᴴ * (bc n).Wᴴ) * ((bc n).Wᴴᴴ * (bc n).Wᴴ) = (bc n).Wᴴᴴ * (bc n).Wᴴ :=
  fun n => by simpa [ctct] using (bc n).hW_tgt
 have hW_tgt_conj : ∀ n, ((bc n).Wᴴ * (bc n).Wᴴᴴ) * ((bc n).Wᴴ * (bc n).Wᴴᴴ) = (bc n).Wᴴ * (bc n).Wᴴᴴ :=
  fun n => by simpa [ctct] using (bc n).hW_src
 have h1WW_n : ∀ n, hsN (1 - (bc n).W * (bc n).Wᴴ) ≤ 2 * ε₀ n * sqrt (d n : ℝ) := by
  intro n
  have h1h : (1 - (bc n).W * (bc n).Wᴴ)ᴴ = 1 - (bc n).W * (bc n).Wᴴ := by
   simp
  have h1p : (1 - (bc n).W * (bc n).Wᴴ) * (1 - (bc n).W * (bc n).Wᴴ) = 1 - (bc n).W * (bc n).Wᴴ := by
   rw [msm, mms, mms, m1m, m1m,
    mm1, (bc n).hW_tgt]; abel
  have hsq : hsSq (1 - (bc n).W * (bc n).Wᴴ) ≤ (2 * ε₀ n * sqrt (d n : ℝ)) ^ 2 := by
   rw [hsSq_tr, h1h, h1p, mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg (d n))]
   have ht := (bc n).hW_tgt_tr; linarith
  have hrt := sqrt_le_sqrt hsq
  rwa [sqrt_sq (by have := hε₀_nn n; positivity)] at hrt
 have hmed_ex : ∀ n, ∃ mu : Fin (bc n).bdBhat.t → ℝ, (∀ k, 0 < mu k) ∧
   let x := ∑ j : Fin (bc n).bdAhat.t, ∑ k : Fin (bc n).bdBhat.t,
    (bFn (mu k) (((bc n).bdAhat.r j : ℝ) / ((bc n).bdAhat.s j : ℝ)) : ℂ) •
     (cPr (bc n).bdAhat j * cPr (bc n).bdBhat k)
   x ∈ (bc n).Ahat ∧ ‖CLM x‖ ≤ 1 ∧ cExp (bc n).Bhat x = ((1 / 2 : ℝ) : ℂ) • 1 :=
  fun n => exists_cond_median (bc n).hBAhat (bc n).bdBhat (bc n).bdAhat
 choose mu hmu_pos hxA₁ hx_norm hx_ce using hmed_ex
 let x (n : ℕ) : Matrix (Fin (bc n).m) (Fin (bc n).m) ℂ :=
  ∑ j : Fin (bc n).bdAhat.t, ∑ k : Fin (bc n).bdBhat.t,
   (bFn (mu n k) (((bc n).bdAhat.r j : ℝ) / ((bc n).bdAhat.s j : ℝ)) : ℂ) •
    (cPr (bc n).bdAhat j * cPr (bc n).bdBhat k)
 let z (n : ℕ) : Matrix (Fin (d n)) (Fin (d n)) ℂ := (bc n).Wᴴ * x n * (bc n).W
 have hzA₀ : ∀ n, z n ∈ A₀ n := fun n => (bc n).hW_conj_Ahat (x n) (hxA₁ n)
 have hzn : ∀ n, ‖CLM (z n)‖ ≤ 1 := fun n => by
  dsimp only [z]
  have h1 := opN_conjPI (bc n).Wᴴ (hW_src_conj n) (x n)
  simp only [ctct] at h1
  exact h1.trans (hx_norm n)
 have hKz_f := (hA₀ z ⟨1, hzn⟩).mpr ⟨z, ⟨1, hzn⟩, hzA₀, by
  have h0 : ∀ n, hsSq (z n - z n) / (d n : ℝ) = 0 := fun n => by rw [sub_self]; simp [hsSq]
  simp_rw [h0]; exact tendsto_const_nhds⟩
 have hKz_t : (∃ C : ℝ, ∀ n, ‖CLM (z n)‖ ≤ C) ∧
   ∀ a, (true || s a) = true →
    Tendsto (fun n => hsSq (U a n * z n - z n * U a n) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
  refine ⟨⟨1, hzn⟩, fun a _ => ?_⟩
  cases hsa : s a
  ·
   obtain ⟨εa, hεa_nn, hεa_tend, hεa_inc⟩ := hconj_inc a hsa
   have hcomm_x : ∀ n, hsN (u' a n * x n - x n * u' a n) ≤
     (15 * εa n + sqrt (6 * εa n + 26 * εa n ^ 2)) * sqrt ((bc n).m : ℝ) := by
    intro n
    have hstep := (no_drift_step (bc n).hBAhat (bc n).bdBhat (bc n).bdAhat
     (hu'U a n) (hu'D a n) (hεa_nn n) (hεa_inc n) (mu n) (hmu_pos n)).1
    have hEq : hsN (u' a n * x n - x n * u' a n) = hsN (x n - (u' a n)ᴴ * x n * u' a n) := by
     have h1 : x n - (u' a n)ᴴ * x n * u' a n = (u' a n)ᴴ * (u' a n * x n - x n * u' a n) := by
      have hUs : (u' a n)ᴴ * u' a n = 1 := star_mul_self_of_mem (hu'U a n)
      rw [mms, ← mma, hUs, m1m, mma]
     have hUm : (u' a n)ᴴᴴ * (u' a n)ᴴ = 1 := by
      rw [ctct, ← star_eq_conjTranspose]
      exact mul_star_self_of_mem (hu'U a n)
     rw [h1, hsN, hsN, hsSq_isoL (u' a n)ᴴ hUm]
    rw [hEq]; exact hstep
   have hcomm_n : Tendsto (fun n => hsN (U a n * z n - z n * U a n) / sqrt (d n : ℝ))
     (hyperfilter ℕ) (𝓝 0) := by
    have hrt_tend : Tendsto (fun n =>
      2 * (hsN (u' a n * (bc n).W - (bc n).W * U a n) / sqrt (d n : ℝ)) +
      sqrt 2 * (15 * εa n + sqrt (6 * εa n + 26 * εa n ^ 2)))
      (hyperfilter ℕ) (𝓝 0) := by
     have hsq : Tendsto (fun n => sqrt (6 * εa n + 26 * εa n ^ 2)) (hyperfilter ℕ) (𝓝 0) := by
      have hpoly : Tendsto (fun n => 6 * εa n + 26 * εa n ^ 2) (hyperfilter ℕ) (𝓝 0) := by
       simpa using (hεa_tend.const_mul 6).add ((hεa_tend.pow 2).const_mul 26)
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hpoly
     have hpart2 : Tendsto (fun n => sqrt 2 * (15 * εa n + sqrt (6 * εa n + 26 * εa n ^ 2)))
       (hyperfilter ℕ) (𝓝 0) := by
      simpa using ((hεa_tend.const_mul 15).add hsq).const_mul (sqrt 2)
     simpa using ((hu'_W_tend a).const_mul 2).add hpart2
    refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg (hsN_nn _) (sqrt_nonneg _))
     ?_ hrt_tend
    filter_upwards [hm_bounds] with n ⟨_, hhi⟩
    have hrt_pos : (0 : ℝ) < sqrt (d n : ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr (hd n))
    rw [div_le_iff₀ hrt_pos]
    have hsplit : U a n * z n - z n * U a n =
      (U a n * (bc n).Wᴴ - (bc n).Wᴴ * u' a n) * x n * (bc n).W +
      (bc n).Wᴴ * (u' a n * x n - x n * u' a n) * (bc n).W +
      (bc n).Wᴴ * x n * (u' a n * (bc n).W - (bc n).W * U a n) := by
     dsimp only [z]
     simp only [msm, mms, mma]; abel
    have ht1 : hsN ((U a n * (bc n).Wᴴ - (bc n).Wᴴ * u' a n) * x n * (bc n).W) ≤
      hsN (u' a n * (bc n).W - (bc n).W * U a n) := by
     have h1 : hsN ((U a n * (bc n).Wᴴ - (bc n).Wᴴ * u' a n) * x n * (bc n).W) ≤
       hsN (U a n * (bc n).Wᴴ - (bc n).Wᴴ * u' a n) := by
      calc
       _ ≤ hsN ((U a n * (bc n).Wᴴ - (bc n).Wᴴ * u' a n) * x n) :=
          hsN_piR (bc n).W (bc n).hW_tgt _
       _ ≤ ‖CLM (x n)‖ * hsN (U a n * (bc n).Wᴴ - (bc n).Wᴴ * u' a n) :=
          hsN_mulR _ (x n)
       _ ≤ 1 * hsN (U a n * (bc n).Wᴴ - (bc n).Wᴴ * u' a n) :=
          mul_le_mul_of_nonneg_right (hx_norm n) (hsN_nn _)
       _ = _ := one_mul _
     have h2 : hsN (U a n * (bc n).Wᴴ - (bc n).Wᴴ * u' a n) =
       hsN (u' a n * (bc n).W - (bc n).W * U a n) := by
      have hid : U a n * (bc n).Wᴴ - (bc n).Wᴴ * u' a n =
        U a n * (u' a n * (bc n).W - (bc n).W * U a n)ᴴ * u' a n := by
       have hUm : U a n * (U a n)ᴴ = 1 := mul_star_self_of_mem (u a n).2
       have hu's : (u' a n)ᴴ * u' a n = 1 := star_mul_self_of_mem (hu'U a n)
       rw [ctS, ctM, ctM,
        mms, msm]
       calc
        U a n * (bc n).Wᴴ - (bc n).Wᴴ * u' a n
         = U a n * (bc n).Wᴴ * ((u' a n)ᴴ * u' a n) -
           (U a n * (U a n)ᴴ) * (bc n).Wᴴ * u' a n := by
           rw [hu's, hUm, mm1, m1m]
        _ = _ := by simp only [mma]
      rw [hid, hsN, hsN,
       hsSq_coisoR (u' a n) (mul_star_self_of_mem (hu'U a n)),
       hsSq_isoL (U a n) (star_mul_self_of_mem (u a n).2),
       hsSq_ct]
     exact h1.trans_eq h2
    have ht2 : hsN ((bc n).Wᴴ * (u' a n * x n - x n * u' a n) * (bc n).W) ≤
      (15 * εa n + sqrt (6 * εa n + 26 * εa n ^ 2)) * (sqrt 2 * sqrt (d n : ℝ)) := by
     have h1 : hsN ((bc n).Wᴴ * (u' a n * x n - x n * u' a n) * (bc n).W) ≤
       hsN (u' a n * x n - x n * u' a n) :=
      (hsN_piR (bc n).W (bc n).hW_tgt _).trans
       (hsN_piL (bc n).Wᴴ (hW_src_conj n) _)
     have hrt_m : sqrt ((bc n).m : ℝ) ≤ sqrt 2 * sqrt (d n : ℝ) := by
      rw [← sqrt_mul zero_le_two]; exact sqrt_le_sqrt hhi
     exact h1.trans ((hcomm_x n).trans
      (mul_le_mul_of_nonneg_left hrt_m (by have := hεa_nn n; positivity)))
    have ht3 : hsN ((bc n).Wᴴ * x n * (u' a n * (bc n).W - (bc n).W * U a n)) ≤
      hsN (u' a n * (bc n).W - (bc n).W * U a n) := by
     rw [mma]
     calc
      hsN ((bc n).Wᴴ * (x n * (u' a n * (bc n).W - (bc n).W * U a n)))
       ≤ hsN (x n * (u' a n * (bc n).W - (bc n).W * U a n)) :=
         hsN_piL (bc n).Wᴴ (hW_src_conj n) _
      _ ≤ ‖CLM (x n)‖ * hsN (u' a n * (bc n).W - (bc n).W * U a n) := hsN_mulL (x n) _
      _ ≤ 1 * hsN (u' a n * (bc n).W - (bc n).W * U a n) :=
         mul_le_mul_of_nonneg_right (hx_norm n) (hsN_nn _)
      _ = _ := one_mul _
    rw [hsplit]
    have htri1 := hsN_add
     ((U a n * (bc n).Wᴴ - (bc n).Wᴴ * u' a n) * x n * (bc n).W +
      (bc n).Wᴴ * (u' a n * x n - x n * u' a n) * (bc n).W)
     ((bc n).Wᴴ * x n * (u' a n * (bc n).W - (bc n).W * U a n))
    have htri2 := hsN_add ((U a n * (bc n).Wᴴ - (bc n).Wᴴ * u' a n) * x n * (bc n).W)
     ((bc n).Wᴴ * (u' a n * x n - x n * u' a n) * (bc n).W)
    have hmul : (2 * (hsN (u' a n * (bc n).W - (bc n).W * U a n) / sqrt (d n : ℝ)) +
      sqrt 2 * (15 * εa n + sqrt (6 * εa n + 26 * εa n ^ 2))) * sqrt (d n : ℝ) =
      2 * hsN (u' a n * (bc n).W - (bc n).W * U a n) +
       (15 * εa n + sqrt (6 * εa n + 26 * εa n ^ 2)) * (sqrt 2 * sqrt (d n : ℝ)) := by
     field_simp [ne_of_gt hrt_pos]
    rw [hmul]; linarith
   exact (tendsto_hsSq_hsN d hd _).mpr hcomm_n
  · exact hKz_f.2 a (by simp [hsa])
 obtain ⟨d0, ⟨Cd, hCd⟩, hd0_mem, hd0_tend⟩ := (hD₀ z ⟨1, hzn⟩).mp hKz_t
 let C_d : ℝ := max Cd 1
 have hC_d_pos : 0 < C_d := lt_of_lt_of_le zero_lt_one (le_max_right Cd 1)
 have hd0_n : ∀ n, ‖CLM (d0 n)‖ ≤ C_d := fun n => (hCd n).trans (le_max_left Cd 1)
 have hd0_n_tend : Tendsto (fun n => hsN (z n - d0 n) / sqrt (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) :=
  (tendsto_hsSq_hsN d hd _).mp hd0_tend
 let η : ℕ → ℝ := fun n =>
  if 0 < (bc n).m then sqrt (hsSq (x n - ((1 / 2 : ℝ) : ℂ) • 1) / ((bc n).m : ℝ)) else 0
 have hη_nn : ∀ n, 0 ≤ η n := fun n => by dsimp only [η]; split_ifs <;> positivity
 have hη_sq : ∀ n, hsSq (x n - ((1 / 2 : ℝ) : ℂ) • 1) ≤ (η n) ^ 2 * ((bc n).m : ℝ) := by
  intro n; dsimp only [η]
  by_cases hm0 : 0 < (bc n).m
  ·
   rw [if_pos hm0, sq_sqrt (div_nonneg (hsSq_nonneg _) (Nat.cast_nonneg _)),
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt hm0))]
  ·
   have hm_eq0 : (bc n).m = 0 := Nat.eq_zero_of_not_pos hm0
   have hz0 : hsSq (x n - ((1 / 2 : ℝ) : ℂ) • 1) = 0 := by
    unfold hsSq; exact sum_eq_zero fun i _ => absurd i.isLt (by omega)
   rw [hz0, hm_eq0]; simp
 have hη_tend : Tendsto η (hyperfilter ℕ) (𝓝 0) := by
  have hx_d1_n : ∀ n, hsN (x n - ((1 / 2 : ℝ) : ℂ) • 1) ≤
    hsN (z n - d0 n) + (4 + 8 * C_d) * ε₀ n * sqrt (d n : ℝ) := by
   intro n
   let d1 := (bc n).πB (d0 n)
   have hd1_mem : d1 ∈ (bc n).Bhat := ((bc n).hBhat_mem d1).mpr ⟨d0 n, hd0_mem n, rfl⟩
   have hce_le : hsN (x n - ((1 / 2 : ℝ) : ℂ) • 1) ≤ hsN (x n - d1) := by
    rw [← hx_ce n]; exact sqrt_le_sqrt (hsSq_sub_condExp_le (bc n).Bhat (x n) hd1_mem)
   have hsplit : x n - d1 =
     (x n - d1) * (1 - (bc n).W * (bc n).Wᴴ) + (1 - (bc n).W * (bc n).Wᴴ) * x n * ((bc n).W * (bc n).Wᴴ) +
     (bc n).W * (z n - d0 n) * (bc n).Wᴴ - (d1 * (bc n).W - (bc n).W * d0 n) * (bc n).Wᴴ := by
    dsimp only [z]
    simp only [mms, msm, mm1, m1m, mma]
    abel
   have hd1_n : ‖CLM d1‖ ≤ C_d := ((bc n).hπB_opNorm (d0 n)).trans (hd0_n n)
   have ht1 : hsN ((x n - d1) * (1 - (bc n).W * (bc n).Wᴴ)) ≤ (1 + C_d) * (2 * ε₀ n * sqrt (d n : ℝ)) := by
    have hclm : ‖CLM (x n - d1)‖ ≤ 1 + C_d := by
     dsimp only [CLM] at hx_norm hd1_n ⊢
     rw [map_sub]; exact (norm_sub_le _ _).trans (by linarith [hx_norm n])
    exact (hsN_mulL _ _).trans (mul_le_mul hclm (h1WW_n n) (hsN_nn _) (by linarith))
   have ht2 : hsN ((1 - (bc n).W * (bc n).Wᴴ) * x n * ((bc n).W * (bc n).Wᴴ)) ≤ 2 * ε₀ n * sqrt (d n : ℝ) := by
    have hPh : ((bc n).W * (bc n).Wᴴ)ᴴ = (bc n).W * (bc n).Wᴴ := by simp
    calc
     hsN (((1 - (bc n).W * (bc n).Wᴴ) * x n) * ((bc n).W * (bc n).Wᴴ))
      = hsN (((bc n).W * (bc n).Wᴴ) * ((1 - (bc n).W * (bc n).Wᴴ) * x n)ᴴ) := by
        rw [← hsN_ct, ctM, hPh]
     _ ≤ hsN (((1 - (bc n).W * (bc n).Wᴴ) * x n)ᴴ) :=
        sqrt_le_sqrt (hsSq_proj_mul_le _ hPh (bc n).hW_tgt _)
     _ = hsN ((1 - (bc n).W * (bc n).Wᴴ) * x n) := hsN_ct _
     _ ≤ ‖CLM (x n)‖ * hsN (1 - (bc n).W * (bc n).Wᴴ) := hsN_mulR _ (x n)
     _ ≤ 2 * ε₀ n * sqrt (d n : ℝ) := by
        nlinarith [hx_norm n, h1WW_n n, hsN_nn (1 - (bc n).W * (bc n).Wᴴ)]
   have ht3 : hsN ((bc n).W * (z n - d0 n) * (bc n).Wᴴ) ≤ hsN (z n - d0 n) :=
    (hsN_piR (bc n).Wᴴ (hW_tgt_conj n) _).trans
     (hsN_piL (bc n).W (bc n).hW_src _)
   have ht4 : hsN ((d1 * (bc n).W - (bc n).W * d0 n) * (bc n).Wᴴ) ≤ C_d * (6 * ε₀ n * sqrt (d n : ℝ)) := by
    have h1 : hsN ((d1 * (bc n).W - (bc n).W * d0 n) * (bc n).Wᴴ) ≤ hsN (d1 * (bc n).W - (bc n).W * d0 n) :=
     hsN_piR (bc n).Wᴴ (hW_tgt_conj n) _
    let d0s := ((C_d⁻¹ : ℝ) : ℂ) • d0 n
    have hd0s_mem : d0s ∈ D₀ n := (D₀ n).smul_mem (hd0_mem n) _
    have hd0s_n : ‖CLM d0s‖ ≤ 1 := by
     dsimp only [d0s, CLM]
     rw [map_smul, norm_smul, norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hC_d_pos)]
     have := hd0_n n; dsimp only [CLM] at this
     rw [inv_mul_le_iff₀ hC_d_pos, mul_one]; exact this
    have happrox := (bc n).hW_approx_B d0s hd0s_mem hd0s_n
    have hscale : d1 * (bc n).W - (bc n).W * d0 n = (C_d : ℂ) • ((bc n).πB d0s * (bc n).W - (bc n).W * d0s) := by
     dsimp only [d1, d0s]
     rw [(bc n).hπB_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_smul,
      ← ofReal_mul, mul_inv_cancel₀ (ne_of_gt hC_d_pos), Complex.ofReal_one, one_smul]
    have h2 : hsN (d1 * (bc n).W - (bc n).W * d0 n) =
      C_d * hsN ((bc n).πB d0s * (bc n).W - (bc n).W * d0s) := by
     rw [hscale, hsNorm_smul, norm_real, Real.norm_eq_abs, abs_of_pos hC_d_pos]
    exact h1.trans (by rw [h2]; exact mul_le_mul_of_nonneg_left happrox (le_of_lt hC_d_pos))
   refine hce_le.trans ?_
   rw [hsplit]
   have htri1 := hsN_sub
    ((x n - d1) * (1 - (bc n).W * (bc n).Wᴴ) + (1 - (bc n).W * (bc n).Wᴴ) * x n * ((bc n).W * (bc n).Wᴴ) +
     (bc n).W * (z n - d0 n) * (bc n).Wᴴ)
    ((d1 * (bc n).W - (bc n).W * d0 n) * (bc n).Wᴴ)
   have htri2 := hsN_add
    ((x n - d1) * (1 - (bc n).W * (bc n).Wᴴ) + (1 - (bc n).W * (bc n).Wᴴ) * x n * ((bc n).W * (bc n).Wᴴ))
    ((bc n).W * (z n - d0 n) * (bc n).Wᴴ)
   have htri3 := hsN_add ((x n - d1) * (1 - (bc n).W * (bc n).Wᴴ))
    ((1 - (bc n).W * (bc n).Wᴴ) * x n * ((bc n).W * (bc n).Wᴴ))
   linarith
  have hupper : Tendsto (fun n => sqrt 2 *
    (hsN (z n - d0 n) / sqrt (d n : ℝ) + (4 + 8 * C_d) * ε₀ n)) (hyperfilter ℕ) (𝓝 0) := by
   simpa using (hd0_n_tend.add (hε₀_tend.const_mul (4 + 8 * C_d))).const_mul (sqrt 2)
  refine squeeze_zero' (Eventually.of_forall hη_nn) ?_ hupper
  filter_upwards [hm_bounds, hm_pos] with n ⟨hlo, _⟩ hmn_pos
  dsimp only [η]; rw [if_pos hmn_pos, sqrt_div (hsSq_nonneg _)]
  change hsN (x n - ((1 / 2 : ℝ) : ℂ) • 1) / sqrt ((bc n).m : ℝ) ≤ _
  have hrt_d_pos : (0 : ℝ) < sqrt (d n : ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr (hd n))
  have hrt_m_pos : (0 : ℝ) < sqrt ((bc n).m : ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr hmn_pos)
  have hrt_m_ge : sqrt (d n : ℝ) / sqrt 2 ≤ sqrt ((bc n).m : ℝ) := by
   rw [← sqrt_div (Nat.cast_nonneg (d n))]; exact sqrt_le_sqrt (by linarith)
  calc
   hsN (x n - ((1 / 2 : ℝ) : ℂ) • 1) / sqrt ((bc n).m : ℝ)
    ≤ (hsN (z n - d0 n) + (4 + 8 * C_d) * ε₀ n * sqrt (d n : ℝ)) / sqrt ((bc n).m : ℝ) :=
      div_le_div_of_nonneg_right (hx_d1_n n) (le_of_lt hrt_m_pos)
   _ ≤ (hsN (z n - d0 n) + (4 + 8 * C_d) * ε₀ n * sqrt (d n : ℝ)) /
      (sqrt (d n : ℝ) / sqrt 2) :=
     div_le_div_of_nonneg_left
      (by have := hε₀_nn n; have := hsN_nn (z n - d0 n); positivity)
      (div_pos hrt_d_pos (sqrt_pos.mpr zero_lt_two)) hrt_m_ge
   _ = sqrt 2 * (hsN (z n - d0 n) / sqrt (d n : ℝ) + (4 + 8 * C_d) * ε₀ n) := by
     field_simp [ne_of_gt hrt_d_pos, ne_of_gt (sqrt_pos.mpr zero_lt_two)]
 exact ⟨mu, η, hmu_pos, hη_nn, hη_tend, hη_sq⟩
lemma oma_conclude_step
  {d : ℕ → ℕ} (hd : ∀ n, 0 < d n) {ι : Type} [Fintype ι] (s : ι → Bool)
  (u : ι → (n : ℕ) → unitaryGroup (Fin (d n)) ℂ)
  {D₀ A₀ : (n : ℕ) → StarSubalgebra ℂ (Matrix (Fin (d n)) (Fin (d n)) ℂ)}
  (hA₀ : ∀ (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ),
   (∃ C : ℝ, ∀ n, ‖CLM (y n)‖ ≤ C) →
   (((∃ C : ℝ, ∀ n, ‖CLM (y n)‖ ≤ C) ∧ ∀ a, (false || s a) = true →
    Tendsto (fun n => hsSq ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
     y n * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)) ↔
    ∃ (a : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ), (∃ C : ℝ, ∀ n, ‖CLM (a n)‖ ≤ C) ∧ (∀ n, a n ∈ A₀ n) ∧
     Tendsto (fun n => hsSq (y n - a n) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)))
  {bdD₀ : (n : ℕ) → BDec (D₀ n)} {bdA₀ : (n : ℕ) → BDec (A₀ n)}
  {ε₀ : ℕ → ℝ} (hε₀_nn : ∀ n, 0 ≤ ε₀ n) (hε₀_tend : Tendsto ε₀ (hyperfilter ℕ) (𝓝 0))
  (bc : (n : ℕ) → BCData (bdD₀ n) (bdA₀ n) (ε₀ n))
  (hm_bounds : ∀ᶠ n in hyperfilter ℕ, (1 / 2 : ℝ) * (d n : ℝ) ≤ ((bc n).m : ℝ) ∧ ((bc n).m : ℝ) ≤ 2 * (d n : ℝ))
  (u' : (n : ℕ) → Matrix (Fin (bc n).m) (Fin (bc n).m) ℂ)
  (hu'U : ∀ n, u' n ∈ unitaryGroup (Fin (bc n).m) ℂ)
  (hu'D : ∀ n, u' n ∈ comm (bc n).Bhat)
  (a : ι)
  (hu'_W_tend : Tendsto (fun n => hsN (u' n * (bc n).W -
   (bc n).W * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) / sqrt (d n : ℝ)) (hyperfilter ℕ) (𝓝 0))
  (εa : ℕ → ℝ) (hεa_nn : ∀ n, 0 ≤ εa n) (hεa_tend : Tendsto εa (hyperfilter ℕ) (𝓝 0))
  (hεa_inc : ∀ n, ∀ b ∈ conjAlg (u' n) (hu'U n) (bc n).Ahat, ‖CLM b‖ ≤ 1 →
   hsSq (b - cExp (bc n).Ahat b) ≤ εa n ^ 2 * ((bc n).m : ℝ))
  (mu : (n : ℕ) → Fin (bc n).bdBhat.t → ℝ) (hmu_pos : ∀ n k, 0 < mu n k)
  (η : ℕ → ℝ) (hη_nn : ∀ n, 0 ≤ η n) (hη_tend : Tendsto η (hyperfilter ℕ) (𝓝 0))
  (hη_sq : ∀ n, hsSq ((∑ j : Fin (bc n).bdAhat.t, ∑ k : Fin (bc n).bdBhat.t,
   (bFn (mu n k) (((bc n).bdAhat.r j : ℝ) / ((bc n).bdAhat.s j : ℝ)) : ℂ) •
    (cPr (bc n).bdAhat j * cPr (bc n).bdBhat k)) -
   ((1 / 2 : ℝ) : ℂ) • 1) ≤ (η n) ^ 2 * ((bc n).m : ℝ))
  (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
  (hKy : (∃ C : ℝ, ∀ n, ‖CLM (y n)‖ ≤ C) ∧ ∀ a', (false || s a') = true →
   Tendsto (fun n => hsSq ((u a' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
    y n * (u a' n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)) :
  (∃ C : ℝ, ∀ n, ‖CLM ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n *
   star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ))‖ ≤ C) ∧ ∀ a', (false || s a') = true →
   Tendsto (fun n => hsSq ((u a' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) *
    ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n * star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) -
    ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n * star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) *
    (u a' n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
 classical
 let U (n : ℕ) : Matrix (Fin (d n)) (Fin (d n)) ℂ := (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)
 have hW_src_conj : ∀ n, ((bc n).Wᴴᴴ * (bc n).Wᴴ) * ((bc n).Wᴴᴴ * (bc n).Wᴴ) = (bc n).Wᴴᴴ * (bc n).Wᴴ :=
  fun n => by simpa [ctct] using (bc n).hW_tgt
 have h1W'W_n : ∀ n, hsN (1 - (bc n).Wᴴ * (bc n).W) ≤ 2 * ε₀ n * sqrt (d n : ℝ) := by
  intro n
  have h1h : (1 - (bc n).Wᴴ * (bc n).W)ᴴ = 1 - (bc n).Wᴴ * (bc n).W := by
   simp
  have h1p : (1 - (bc n).Wᴴ * (bc n).W) * (1 - (bc n).Wᴴ * (bc n).W) = 1 - (bc n).Wᴴ * (bc n).W := by
   rw [msm, mms, mms, m1m, m1m,
    mm1, (bc n).hW_src]; abel
  have hsq : hsSq (1 - (bc n).Wᴴ * (bc n).W) ≤ (2 * ε₀ n * sqrt (d n : ℝ)) ^ 2 := by
   rw [hsSq_tr, h1h, h1p, mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg (d n))]
   have h0 : 0 ≤ ε₀ n ^ 2 * (d n : ℝ) := mul_nonneg (sq_nonneg (ε₀ n)) (Nat.cast_nonneg (d n))
   have ht := (bc n).hW_src_tr; linarith
  have hrt := sqrt_le_sqrt hsq
  rwa [sqrt_sq (by have := hε₀_nn n; positivity)] at hrt
 obtain ⟨a0, ⟨Ca, hCa⟩, ha0_mem, ha0_tend⟩ := (hA₀ y hKy.1).mp hKy
 let C_a : ℝ := max Ca 1
 have hC_a_pos : 0 < C_a := lt_of_lt_of_le zero_lt_one (le_max_right Ca 1)
 have ha0_n : ∀ n, ‖CLM (a0 n)‖ ≤ C_a := fun n => (hCa n).trans (le_max_left Ca 1)
 have hB_tgt : ∃ C : ℝ, ∀ n, ‖CLM (U n * y n * star (U n))‖ ≤ C := by
  obtain ⟨Cy, hCy⟩ := hKy.1
  refine ⟨Cy, fun n => ?_⟩
  have h1 := opNorm_conj_unitary (Unitary.star_mem (u a n).2) (y n)
  have h2 : ‖CLM (U n * y n * star (U n))‖ = ‖CLM (y n)‖ := by
   simpa [U, star_eq_conjTranspose, ctct] using h1
  rw [h2]; exact hCy n
 refine (hA₀ _ hB_tgt).mpr ?_
 let a1 (n : ℕ) : Matrix (Fin (bc n).m) (Fin (bc n).m) ℂ := (bc n).W * a0 n * (bc n).Wᴴ
 have ha1_mem : ∀ n, a1 n ∈ (bc n).Ahat := fun n => (bc n).hW_conj_A (a0 n) (ha0_mem n)
 have ha1_n : ∀ n, ‖CLM (a1 n)‖ ≤ C_a := fun n =>
  (opN_conjPI (bc n).W (bc n).hW_src _).trans (ha0_n n)
 let Ba (n : ℕ) := conjAlg (u' n) (hu'U n) (bc n).Ahat
 let b1 (n : ℕ) : Matrix (Fin (bc n).m) (Fin (bc n).m) ℂ := cExp (Ba n) (a1 n)
 have hb1_mem : ∀ n, b1 n ∈ Ba n := fun n => condExp_mem (Ba n) (a1 n)
 have hb1_n : ∀ n, ‖CLM (b1 n)‖ ≤ C_a := fun n => (opNorm_condExp_le (Ba n) (a1 n)).trans (ha1_n n)
 let c1 (n : ℕ) : Matrix (Fin (bc n).m) (Fin (bc n).m) ℂ := u' n * b1 n * (u' n)ᴴ
 have hc1_mem : ∀ n, c1 n ∈ (bc n).Ahat := fun n => hb1_mem n
 have hc1_n : ∀ n, ‖CLM (c1 n)‖ ≤ C_a := fun n => by
  dsimp only [c1]
  have h1 := opNorm_conj_unitary (Unitary.star_mem (hu'U n)) (b1 n)
  have h2 : ‖CLM (u' n * b1 n * (u' n)ᴴ)‖ = ‖CLM (b1 n)‖ := by
   simpa [star_eq_conjTranspose, ctct] using h1
  rw [h2]; exact hb1_n n
 let a_out (n : ℕ) : Matrix (Fin (d n)) (Fin (d n)) ℂ := (bc n).Wᴴ * c1 n * (bc n).W
 have ha_out_mem : ∀ n, a_out n ∈ A₀ n := fun n => (bc n).hW_conj_Ahat (c1 n) (hc1_mem n)
 have ha_out_n : ∀ n, ‖CLM (a_out n)‖ ≤ C_a := fun n => by
  dsimp only [a_out]
  have h1 := opN_conjPI (bc n).Wᴴ (hW_src_conj n) (c1 n)
  simp only [ctct] at h1
  exact h1.trans (hc1_n n)
 refine ⟨a_out, ⟨C_a, ha_out_n⟩, ha_out_mem, ?_⟩
 let errB (n : ℕ) : ℝ :=
  sqrt (128 * (2 * η n + 10 * εa n + sqrt (6 * εa n + 26 * εa n ^ 2)) * (1 + 2 * εa n)) +
   12 * εa n
 have herrB_nn : ∀ n, 0 ≤ errB n := fun n => by dsimp only [errB]; have := hεa_nn n; positivity
 have herrB_tend : Tendsto errB (hyperfilter ℕ) (𝓝 0) := by
  dsimp only [errB]
  have hsq1 : Tendsto (fun n => sqrt (6 * εa n + 26 * εa n ^ 2)) (hyperfilter ℕ) (𝓝 0) := by
   have hpoly : Tendsto (fun n => 6 * εa n + 26 * εa n ^ 2) (hyperfilter ℕ) (𝓝 0) := by
    simpa using (hεa_tend.const_mul 6).add ((hεa_tend.pow 2).const_mul 26)
   simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hpoly
  have hmid : Tendsto (fun n => 2 * η n + 10 * εa n + sqrt (6 * εa n + 26 * εa n ^ 2))
    (hyperfilter ℕ) (𝓝 0) := by
   simpa using ((hη_tend.const_mul 2).add (hεa_tend.const_mul 10)).add hsq1
  have hfac : Tendsto (fun n => 1 + 2 * εa n) (hyperfilter ℕ) (𝓝 1) := by
   simpa using tendsto_const_nhds.add (hεa_tend.const_mul 2)
  have hprod : Tendsto (fun n =>
    128 * (2 * η n + 10 * εa n + sqrt (6 * εa n + 26 * εa n ^ 2)) * (1 + 2 * εa n))
    (hyperfilter ℕ) (𝓝 0) := by
   simpa using (hmid.const_mul 128).mul hfac
  have hsq2 : Tendsto (fun n => sqrt
    (128 * (2 * η n + 10 * εa n + sqrt (6 * εa n + 26 * εa n ^ 2)) * (1 + 2 * εa n)))
    (hyperfilter ℕ) (𝓝 0) := by
   simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hprod
  simpa using hsq2.add (hεa_tend.const_mul 12)
 have ha1_b1_le : ∀ n, hsN (a1 n - b1 n) ≤ C_a * errB n * sqrt ((bc n).m : ℝ) := by
  intro n
  let a1s := ((C_a⁻¹ : ℝ) : ℂ) • a1 n
  have ha1s_mem : a1s ∈ (bc n).Ahat := ((bc n).Ahat).smul_mem (ha1_mem n) _
  have ha1s_n : ‖CLM a1s‖ ≤ 1 := by
   dsimp only [a1s, CLM]
   rw [map_smul, norm_smul, norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hC_a_pos)]
   have := ha1_n n; dsimp only [CLM] at this
   rw [inv_mul_le_iff₀ hC_a_pos, mul_one]; exact this
  have hstep := (no_drift_step (bc n).hBAhat (bc n).bdBhat (bc n).bdAhat
   (hu'U n) (hu'D n) (hεa_nn n) (hεa_inc n) (mu n) (hmu_pos n)).2
   (hη_nn n) (hη_sq n) a1s ha1s_mem ha1s_n
  have hscale : a1 n - b1 n = (C_a : ℂ) • (a1s - cExp (Ba n) a1s) := by
   dsimp only [b1, a1s, Ba]
   rw [LinearMap.map_smul, ← smul_sub, smul_smul, ← ofReal_mul,
    mul_inv_cancel₀ (ne_of_gt hC_a_pos), Complex.ofReal_one, one_smul]
  rw [hscale, hsNorm_smul, norm_real, Real.norm_eq_abs, abs_of_pos hC_a_pos, mul_assoc]
  exact mul_le_mul_of_nonneg_left hstep (le_of_lt hC_a_pos)
 have hya0_n : Tendsto (fun n => hsN (y n - a0 n) / sqrt (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) :=
  (tendsto_hsSq_hsN d hd _).mp ha0_tend
 have hfinal_n : Tendsto (fun n => hsN (U n * y n * star (U n) - a_out n) / sqrt (d n : ℝ))
   (hyperfilter ℕ) (𝓝 0) := by
  have hupper : Tendsto (fun n =>
    hsN (y n - a0 n) / sqrt (d n : ℝ) +
    C_a * (sqrt 2 * errB n) +
    2 * C_a * (hsN (u' n * (bc n).W - (bc n).W * U n) / sqrt (d n : ℝ) + 2 * ε₀ n))
    (hyperfilter ℕ) (𝓝 0) := by
   have hp2 : Tendsto (fun n => C_a * (sqrt 2 * errB n)) (hyperfilter ℕ) (𝓝 0) := by
    simpa using (herrB_tend.const_mul (sqrt 2)).const_mul C_a
   have hp3 : Tendsto (fun n => 2 * C_a *
     (hsN (u' n * (bc n).W - (bc n).W * U n) / sqrt (d n : ℝ) + 2 * ε₀ n))
     (hyperfilter ℕ) (𝓝 0) := by
    simpa using (hu'_W_tend.add (hε₀_tend.const_mul 2)).const_mul (2 * C_a)
   simpa using (hya0_n.add hp2).add hp3
  refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg (hsN_nn _) (sqrt_nonneg _))
   ?_ hupper
  filter_upwards [hm_bounds] with n ⟨_, hhi⟩
  have hrt_pos : (0 : ℝ) < sqrt (d n : ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr (hd n))
  rw [div_le_iff₀ hrt_pos]
  let S := (bc n).Wᴴ * u' n * (bc n).W
  have hSU : hsN (S - U n) ≤
    hsN (u' n * (bc n).W - (bc n).W * U n) + 2 * ε₀ n * sqrt (d n : ℝ) := by
   have hsp : S - U n = (bc n).Wᴴ * (u' n * (bc n).W - (bc n).W * U n) - (1 - (bc n).Wᴴ * (bc n).W) * U n := by
    dsimp only [S]; simp only [mms, msm, m1m, mma]; abel
   rw [hsp]
   have h1 : hsN ((bc n).Wᴴ * (u' n * (bc n).W - (bc n).W * U n)) ≤
     hsN (u' n * (bc n).W - (bc n).W * U n) :=
    hsN_piL (bc n).Wᴴ (hW_src_conj n) _
   have h2 : hsN ((1 - (bc n).Wᴴ * (bc n).W) * U n) ≤ 2 * ε₀ n * sqrt (d n : ℝ) := by
    have h0 : hsN ((1 - (bc n).Wᴴ * (bc n).W) * U n) = hsN (1 - (bc n).Wᴴ * (bc n).W) := by
     rw [hsN, hsN, hsSq_coisoR (U n) (mul_star_self_of_mem (u a n).2)]
    rw [h0]; exact h1W'W_n n
   exact (hsN_sub _ _).trans (by linarith)
  have hS_conj : S * a0 n * Sᴴ = (bc n).Wᴴ * (u' n * a1 n * (u' n)ᴴ) * (bc n).W := by
   dsimp only [S, a1]
   simp only [ctM, ctct, mma]
  have hsplit : U n * y n * star (U n) - a_out n =
    U n * (y n - a0 n) * (U n)ᴴ + (U n - S) * a0 n * (U n)ᴴ + S * a0 n * ((U n)ᴴ - Sᴴ) +
     (bc n).Wᴴ * (u' n * (a1 n - b1 n) * (u' n)ᴴ) * (bc n).W := by
   dsimp only [a_out, c1]
   rw [star_eq_conjTranspose]
   simp only [mms, msm]
   rw [← hS_conj]; abel
  have hU_co : (U n)ᴴ * (U n)ᴴᴴ = 1 := by
   rw [ctct, ← star_eq_conjTranspose]
   exact star_mul_self_of_mem (u a n).2
  have hu'_co : (u' n)ᴴ * (u' n)ᴴᴴ = 1 := by
   rw [ctct, ← star_eq_conjTranspose]
   exact star_mul_self_of_mem (hu'U n)
  have ht1 : hsN (U n * (y n - a0 n) * (U n)ᴴ) = hsN (y n - a0 n) := by
   rw [hsN, hsN, hsSq_coisoR (U n)ᴴ hU_co,
    hsSq_isoL (U n) (star_mul_self_of_mem (u a n).2)]
  have ht2 : hsN ((U n - S) * a0 n * (U n)ᴴ) ≤ C_a * hsN (S - U n) := by
   have h0 : hsN ((U n - S) * a0 n * (U n)ᴴ) = hsN ((U n - S) * a0 n) := by
    rw [hsN, hsN, hsSq_coisoR (U n)ᴴ hU_co]
   rw [h0]
   have h1 := hsN_mulR (U n - S) (a0 n)
   have h2 : hsN (U n - S) = hsN (S - U n) := by rw [← hsNorm_neg, neg_sub]
   rw [h2] at h1
   exact h1.trans (mul_le_mul_of_nonneg_right (ha0_n n) (hsN_nn _))
  have ht3 : hsN (S * a0 n * ((U n)ᴴ - Sᴴ)) ≤ C_a * hsN (S - U n) := by
   have hS_op : ‖CLM S‖ ≤ 1 := by
    dsimp only [S]
    have h1 := opN_conjPI (bc n).Wᴴ (hW_src_conj n) (u' n)
    simp only [ctct] at h1
    exact h1.trans (opNorm_unitary_le' (hu'U n))
   rw [mma]
   calc
    hsN (S * (a0 n * ((U n)ᴴ - Sᴴ)))
     ≤ ‖CLM S‖ * hsN (a0 n * ((U n)ᴴ - Sᴴ)) := hsN_mulL S _
    _ ≤ 1 * (C_a * hsN ((U n)ᴴ - Sᴴ)) :=
       mul_le_mul hS_op
        ((hsN_mulL (a0 n) _).trans (mul_le_mul_of_nonneg_right (ha0_n n) (hsN_nn _)))
        (hsN_nn _) zero_le_one
    _ = C_a * hsN (S - U n) := by
       rw [one_mul, ← ctS, hsN_ct, ← hsNorm_neg, neg_sub]
  have ht4 : hsN ((bc n).Wᴴ * (u' n * (a1 n - b1 n) * (u' n)ᴴ) * (bc n).W) ≤
    C_a * (sqrt 2 * errB n) * sqrt (d n : ℝ) := by
   have h1 : hsN ((bc n).Wᴴ * (u' n * (a1 n - b1 n) * (u' n)ᴴ) * (bc n).W) ≤ hsN (a1 n - b1 n) := by
    calc
     _ ≤ hsN (u' n * (a1 n - b1 n) * (u' n)ᴴ) :=
        (hsN_piR (bc n).W (bc n).hW_tgt _).trans
         (hsN_piL (bc n).Wᴴ (hW_src_conj n) _)
     _ = hsN (a1 n - b1 n) := by
        rw [hsN, hsN, hsSq_coisoR (u' n)ᴴ hu'_co,
         hsSq_isoL (u' n) (star_mul_self_of_mem (hu'U n))]
   have hrt_m : sqrt ((bc n).m : ℝ) ≤ sqrt 2 * sqrt (d n : ℝ) := by
    rw [← sqrt_mul zero_le_two]; exact sqrt_le_sqrt hhi
   calc
    hsN ((bc n).Wᴴ * (u' n * (a1 n - b1 n) * (u' n)ᴴ) * (bc n).W)
     ≤ C_a * errB n * sqrt ((bc n).m : ℝ) := h1.trans (ha1_b1_le n)
    _ ≤ C_a * errB n * (sqrt 2 * sqrt (d n : ℝ)) :=
      mul_le_mul_of_nonneg_left hrt_m (mul_nonneg (le_of_lt hC_a_pos) (herrB_nn n))
    _ = C_a * (sqrt 2 * errB n) * sqrt (d n : ℝ) := by ring
  rw [hsplit]
  have htri1 := hsN_add
   (U n * (y n - a0 n) * (U n)ᴴ + (U n - S) * a0 n * (U n)ᴴ + S * a0 n * ((U n)ᴴ - Sᴴ))
   ((bc n).Wᴴ * (u' n * (a1 n - b1 n) * (u' n)ᴴ) * (bc n).W)
  have htri2 := hsN_add
   (U n * (y n - a0 n) * (U n)ᴴ + (U n - S) * a0 n * (U n)ᴴ) (S * a0 n * ((U n)ᴴ - Sᴴ))
  have htri3 := hsN_add (U n * (y n - a0 n) * (U n)ᴴ) ((U n - S) * a0 n * (U n)ᴴ)
  have hmul : (hsN (y n - a0 n) / sqrt (d n : ℝ) + C_a * (sqrt 2 * errB n) +
    2 * C_a * (hsN (u' n * (bc n).W - (bc n).W * U n) / sqrt (d n : ℝ) + 2 * ε₀ n)) *
    sqrt (d n : ℝ) =
    hsN (y n - a0 n) + C_a * (sqrt 2 * errB n) * sqrt (d n : ℝ) +
     2 * C_a * (hsN (u' n * (bc n).W - (bc n).W * U n) + 2 * ε₀ n * sqrt (d n : ℝ)) := by
   field_simp [ne_of_gt hrt_pos]
  rw [hmul]; nlinarith [hSU, hC_a_pos]
 exact (tendsto_hsSq_hsN d hd _).mpr hfinal_n
end NoDrift
end
end OMA.Green100H4
open Filter Matrix OMA.Green100H4
open scoped Topology
theorem OMA.solution : OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.H4 := by
 classical
 intro d hd ι _ s u
 dsimp only
 intro hIf hIt hconj
 obtain ⟨A₀, hA₀⟩ := hIf
 obtain ⟨D₀, hD₀⟩ := hIt
 obtain ⟨ε₀, hε₀_nn, hε₀_tend, hD₀_inc⟩ := uniform_near_inclusion d
  (Eventually.of_forall hd) D₀ A₀ fun b hb hbn => by
   have hBb : ∃ C : ℝ, ∀ n, ‖CLM (b n)‖ ≤ C := ⟨1, hbn⟩
   have hKb := (hD₀ b hBb).mpr ⟨b, hBb, hb, by
    have h0 : ∀ n, (∑ i, ∑ j, ‖(b n - b n) i j‖ ^ 2) / (d n : ℝ) = 0 := fun n => by simp
    simp_rw [h0]; exact tendsto_const_nhds⟩
   obtain ⟨a, _, haA, ha_tend⟩ := (hA₀ b hBb).mp ⟨hKb.1, fun a _ => hKb.2 a rfl⟩
   exact ⟨a, haA, ha_tend⟩
 let bdD₀ (n : ℕ) := (exists_blockDecomp (D₀ n)).some
 let bdA₀ (n : ℕ) := (exists_blockDecomp (A₀ n)).some
 let bc (n : ℕ) := (exists_bratteliCorrection (bdD₀ n) (bdA₀ n) (hε₀_nn n) (hD₀_inc n)).some
 have hm_bounds : ∀ᶠ n in hyperfilter ℕ,
   (1 / 2 : ℝ) * (d n : ℝ) ≤ ((bc n).m : ℝ) ∧ ((bc n).m : ℝ) ≤ 2 * (d n : ℝ) := by
  have h1 : ∀ᶠ n in hyperfilter ℕ, ε₀ n < 1 / 2 :=
   hε₀_tend.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [h1] with n hn
  have hdiff := (bc n).hm_diff
  rw [abs_le] at hdiff
  have hsq : 2 * ε₀ n ^ 2 ≤ 1 / 2 := by nlinarith [hε₀_nn n]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (d n)]
 have hm_pos : ∀ᶠ n in hyperfilter ℕ, 0 < (bc n).m := by
  filter_upwards [hm_bounds] with n ⟨hlo, _⟩
  have hdpos : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.mpr (hd n)
  exact Nat.cast_pos (α := ℝ).mp (by linarith)
 obtain ⟨u', hu'U, hu'D, hu'_M₀_tend, hu'_W_tend⟩ :=
  oma_round_tendsto hd s u hD₀ hε₀_nn hε₀_tend bc
 have hconj_inc : ∀ a, s a = false →
   ∃ εa : ℕ → ℝ, (∀ n, 0 ≤ εa n) ∧ Tendsto εa (hyperfilter ℕ) (𝓝 0) ∧
    ∀ n, ∀ b ∈ conjAlg (u' a n) (hu'U a n) (bc n).Ahat, ‖CLM b‖ ≤ 1 →
     hsSq (b - cExp (bc n).Ahat b) ≤ εa n ^ 2 * ((bc n).m : ℝ) :=
  fun a ha => oma_conj_near_inclusion hd s u hA₀ hconj bc hm_bounds hm_pos (u' a) (hu'U a) a ha (hu'_M₀_tend a)
 obtain ⟨mu, η, hmu_pos, hη_nn, hη_tend, hη_sq⟩ :=
  oma_median_limit hd s u hA₀ hD₀ hε₀_nn hε₀_tend bc hm_bounds hm_pos u' hu'U hu'D hu'_W_tend hconj_inc
 intro a ha y hKy
 obtain ⟨εa, hεa_nn, hεa_tend, hεa_inc⟩ := hconj_inc a ha
 exact oma_conclude_step hd s u hA₀ hε₀_nn hε₀_tend bc hm_bounds (u' a) (hu'U a) (hu'D a)
  a (hu'_W_tend a) εa hεa_nn hεa_tend hεa_inc mu hmu_pos η hη_nn hη_tend hη_sq y hKy
