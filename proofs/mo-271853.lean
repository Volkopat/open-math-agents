import OMAStatements.S_mo_271853

/-!
Complete proof by @connoranderson, linked from statement PR #25918 and desk DONE #119232.
Pinned companion:
https://github.com/connoranderson/open-math-agents/blob/61f3a1a6e0e6ee0973eb6c37499235c283fc3ee7/proofs/mo-271853.lean
All mathematical source is retained unchanged; this port adds attribution and validation.
Source: Conner DiPaolo, https://mathoverflow.net/questions/271853 (CC BY-SA 3.0).
Credit Suvrit for the block SDP and positive definite case, and fedja for the diagonal strategy.
This registers existing proof work and claims no new mathematical discovery.
The sharp factor is for spectral-norm loss from the Frobenius projection; the registered
closed-form optimizer concerns X=I and positive definite Y.
-/

namespace OMA.S_mo_271853
open Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

private lemma sdp_one {m n : ℕ} (R : Mat m n) :
    ‖R‖ ≤ 1 ↔ (fromBlocks (1:Mat m m) R Rᴴ (1:Mat n n)).PosSemidef := by
  let : Invertible (1:Mat m m) := invertibleOne
  rw [Matrix.PosDef.fromBlocks₁₁ R _ Matrix.PosDef.one, inv_one, Matrix.mul_one,
    ← Matrix.nonneg_iff_posSemidef, sub_nonneg]
  have hs := CStarAlgebra.norm_le_iff_le_algebraMap (Rᴴ*R) (show (0:ℝ) ≤ 1 by norm_num)
    (Matrix.posSemidef_conjTranspose_mul_self R).nonneg
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, map_one] at hs
  rw [← hs]
  constructor
  · intro h
    nlinarith [norm_nonneg R]
  · intro h
    nlinarith [norm_nonneg R]

lemma sdp {m n : ℕ} (R : Mat m n) (t : ℝ) (ht : 0≤t) :
    ‖R‖ ≤ t ↔ (fromBlocks ((t:ℂ) • (1:Mat m m)) R Rᴴ ((t:ℂ) • (1:Mat n n))).PosSemidef := by
  rcases ht.eq_or_lt with rfl|hpos
  · simp only [Complex.ofReal_zero, zero_smul, norm_le_zero_iff]
    constructor
    · rintro rfl
      simp [fromBlocks_zero, Matrix.PosSemidef.zero]
    · intro hb
      have htrace : (fromBlocks (0:Mat m m) R Rᴴ (0:Mat n n)).trace = 0 := by
        simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
      have hz := hb.trace_eq_zero_iff.mp htrace
      ext i j
      exact congrArg (fun M => M (Sum.inl i) (Sum.inr j)) hz
  · let Q : Mat m n := (t:ℂ)⁻¹ • R
    have hc : (t:ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hblock : (t:ℂ) • fromBlocks (1:Mat m m) Q Qᴴ (1:Mat n n) =
        fromBlocks ((t:ℂ) • (1:Mat m m)) R Rᴴ ((t:ℂ) • (1:Mat n n)) := by
      rw [fromBlocks_smul]
      simp [Q, smul_smul, hc, Matrix.conjTranspose_smul]
    have hnorm : ‖Q‖ = t⁻¹ * ‖R‖ := by
      simp [Q, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    rw [← hblock]
    have hnon : (0:ℂ) ≤ t := Complex.zero_le_real.mpr hpos.le
    have hnon' : (0:ℂ) ≤ (t:ℂ)⁻¹ := by simpa using (Complex.zero_le_real.mpr (inv_nonneg.mpr hpos.le))
    have iffQ : ‖R‖ ≤ t ↔ ‖Q‖ ≤ 1 := by
      rw [hnorm, ← div_eq_inv_mul, div_le_one hpos]
    rw [iffQ, sdp_one]
    constructor
    · intro h
      exact h.smul hnon
    · intro h
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h.smul hnon'

end OMA.S_mo_271853

namespace OMA.S_mo_271853
open Matrix Finset
open scoped Matrix.Norms.L2Operator InnerProductSpace

private def flatten {m n : ℕ} : Mat m n →ₗ[ℂ] EuclideanSpace ℂ (Fin m × Fin n) where
  toFun A := WithLp.toLp 2 (fun i => A i.1 i.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma flatten_injective {m n : ℕ} : Function.Injective (flatten (m:=m) (n:=n)) := by
  intro A B h
  exact Matrix.ext fun i j => congrArg (fun x : EuclideanSpace ℂ (Fin m × Fin n) => x (i,j)) h

private lemma flatten_sq {m n : ℕ} (A : Mat m n) :
    ‖flatten A‖^2 = ∑ i, ∑ j, ‖A i j‖^2 := by
  rw [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]
  rfl

private lemma op_le_flatten {m n : ℕ} (A : Mat m n) : ‖A‖ ≤ ‖flatten A‖ := by
  rw [l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp v)‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [EuclideanSpace.norm_sq_eq,mul_pow,flatten_sq,EuclideanSpace.norm_sq_eq,sum_mul]
  apply sum_le_sum
  intro i _
  change ‖∑ j, A i j * v j‖^2 ≤ _
  calc ‖∑ j, A i j * v j‖^2 ≤ (∑ j, ‖A i j‖*‖v j‖)^2 := by
         apply pow_le_pow_left₀ (norm_nonneg _)
         simpa only [norm_mul] using norm_sum_le (univ : Finset (Fin n)) (fun j => A i j * v j)
    _ ≤ _ := sum_mul_sq_le_sq_mul_sq univ (fun j => ‖A i j‖) (fun j => ‖v j‖)

private lemma flatten_col {m n : ℕ} (A : Mat m n) : ‖flatten A‖^2 ≤ (n:ℝ)*‖A‖^2 := by
  rw [flatten_sq,sum_comm]
  have hc (j : Fin n) : (∑ i, ‖A i j‖^2) ≤ ‖A‖^2 := by
    let v : EuclideanSpace ℂ (Fin n) := PiLp.single 2 j 1
    have hv : ‖v‖ = 1 := by simp [v]
    have h := A.l2_opNorm_mulVec v
    rw [hv,mul_one] at h
    have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [EuclideanSpace.norm_sq_eq] at hh
    simp only [v,PiLp.ofLp_single,Matrix.mulVec_single_one,EuclideanSpace.equiv,
      PiLp.coe_symm_continuousLinearEquiv,WithLp.ofLp_toLp,Matrix.col_apply] at hh
    exact hh
  calc ∑ j,∑ i,‖A i j‖^2 ≤ ∑ _j : Fin n, ‖A‖^2 := sum_le_sum fun j _ => hc j
    _ = _ := by simp

private lemma flatten_op {m n : ℕ} (A : Mat m n) :
    ‖flatten A‖ ≤ Real.sqrt (min m n)*‖A‖ := by
  have ht : ‖flatten Aᴴ‖^2 = ‖flatten A‖^2 := by
    rw [flatten_sq,flatten_sq,sum_comm]
    simp [conjTranspose_apply]
  have hm := flatten_col Aᴴ
  rw [ht,l2_opNorm_conjTranspose] at hm
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity)]
  rcases le_total m n with he | he
  · simpa only [min_eq_left (show (m:ℝ) ≤ n by exact_mod_cast he)] using hm
  · simpa only [min_eq_right (show (n:ℝ) ≤ m by exact_mod_cast he)] using flatten_col A

private lemma flat_projection {m n : ℕ} (X Y : Mat m n) :
    (ℂ ∙ flatten Y).starProjection (flatten X) = flatten (coef X Y • Y) := by
  rw [Submodule.starProjection_singleton,map_smul,flatten_sq]
  congr 1
  unfold coef
  congr 1
  rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fintype.sum_prod_type]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_comm _ _

lemma loss {m n : ℕ} (_hm : 1 ≤ m) (_hn : 1 ≤ n) (X Y : Mat m n) (z : ℂ) :
    ‖X - coef X Y • Y‖ ≤ ((1+Real.sqrt (min m n))/2) * ‖X-z•Y‖ := by
  let R := X-z•Y
  let P := coef R Y • Y
  let K := ℂ ∙ flatten Y
  have hz : K.starProjection (flatten (z•Y)) = flatten (z•Y) := by
    apply Submodule.starProjection_eq_self_iff.mpr
    rw [map_smul]
    exact K.smul_mem z (Submodule.mem_span_singleton_self _)
  have hR : X - coef X Y • Y = R - P := by
    apply flatten_injective
    simp only [map_sub,P,←flat_projection]
    change flatten X - K.starProjection (flatten X) =
      flatten R - K.starProjection (flatten R)
    simp only [R,map_sub,hz]
    abel
  have hS : ‖flatten (R-(P+P))‖ = ‖flatten R‖ := by
    rw [map_sub,map_add, norm_sub_rev]
    change ‖flatten (coef R Y • Y) + flatten (coef R Y • Y) - flatten R‖ = _
    rw [← flat_projection, ← two_nsmul, ← Submodule.reflection_apply]
    exact K.reflection.norm_map (flatten R)
  have bound := (op_le_flatten (R-(P+P))).trans (hS.le.trans (flatten_op R))
  have htri := norm_add_le R (R-(P+P))
  rw [show R+(R-(P+P))=(R-P)+(R-P) by abel, ←two_nsmul, ←Nat.cast_smul_eq_nsmul ℂ, norm_smul] at htri
  rw [hR]
  change ‖R-P‖ ≤ ((1+Real.sqrt (min m n))/2)*‖R‖
  norm_num only [Nat.cast_ofNat,Complex.norm_ofNat] at htri
  linarith

end OMA.S_mo_271853

namespace OMA.S_mo_271853
open Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder

lemma diag_res_norm {n : ℕ} (d : Fin n → ℂ) (z : ℂ) :
    ‖(1:Mat n n) - z • diagonal d‖ = ‖fun i => 1-z*d i‖ := by
  have he : (1:Mat n n) - z • diagonal d = diagonal (fun i => 1-z*d i) := by
    ext i j
    by_cases h : i=j
    · subst j; simp [smul_eq_mul]
    · simp [h,Matrix.sub_apply,Matrix.smul_apply]
  rw [he,Matrix.l2_opNorm_diagonal]

private lemma herm_res_norm {n : ℕ} {Y : Mat n n} (hY : Y.IsHermitian) (z : ℂ) :
    ‖(1:Mat n n) - z • Y‖ = ‖fun i => 1-z*(hY.eigenvalues i:ℂ)‖ := by
  let U := hY.eigenvectorUnitary
  let E := Unitary.conjStarAlgAut ℂ (Mat n n) U
  let D := diagonal (fun i => (hY.eigenvalues i:ℂ))
  have he : E D = Y := hY.spectral_theorem.symm
  have he' : E (1-z•D) = 1-z•Y := by rw [map_sub,map_one,map_smul,he]
  rw [←he']
  calc ‖E (1-z•D)‖ = ‖((U:Mat n n)*(1-z•D))*(star U:Mat n n)‖ := rfl
    _ = ‖(1:Mat n n) - z•D‖ := by
      exact (CStarRing.norm_mul_coe_unitary _ (star U)).trans (CStarRing.norm_coe_unitary_mul U _)
    _ = _ := diag_res_norm _ _

lemma positive_case (n : ℕ) (Y : Mat n n) (hY : Y.IsHermitian) (lo hi : ℝ) (hl : 0<lo)
    (hall : ∀ i, lo≤hY.eigenvalues i ∧ hY.eigenvalues i≤hi)
    (hlo : ∃ i, hY.eigenvalues i=lo) (hhi : ∃ j, hY.eigenvalues j=hi) :
    ‖(1:Mat n n)-((2/(lo+hi):ℝ):ℂ) • Y‖=(hi-lo)/(hi+lo) ∧
      ∀ z : ℂ, (hi-lo)/(hi+lo)≤‖(1:Mat n n)-z•Y‖ := by
  obtain ⟨i,hi'⟩ := hlo
  obtain ⟨j,hj'⟩ := hhi
  have hlh : lo≤hi := hi' ▸ (hall i).2
  have hh : 0<hi := hl.trans_le hlh
  have hp : 0<hi+lo := by linarith
  have hq : 0<lo+hi := by linarith
  have hn : 0 ≤ (hi-lo)/(hi+lo) := div_nonneg (sub_nonneg.mpr hlh) hp.le
  have lower (z : ℂ) : (hi-lo)/(hi+lo) ≤ ‖(1:Mat n n)-z•Y‖ := by
    rw [herm_res_norm hY]
    let R := ‖fun t => (1:ℂ)-z*(hY.eigenvalues t:ℂ)‖
    have ha : ‖1-z*(lo:ℂ)‖ ≤ R := by
      simpa only [hi'] using (norm_le_pi_norm (fun t => (1:ℂ)-z*(hY.eigenvalues t:ℂ)) i)
    have hb : ‖1-z*(hi:ℂ)‖ ≤ R := by
      simpa only [hj'] using (norm_le_pi_norm (fun t => (1:ℂ)-z*(hY.eigenvalues t:ℂ)) j)
    have he : ((hi-lo:ℝ):ℂ) = hi*(1-z*lo)-lo*(1-z*hi) := by push_cast; ring
    have ht := norm_sub_le ((hi:ℂ)*(1-z*lo)) ((lo:ℂ)*(1-z*hi))
    rw [←he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hlh)] at ht
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hl,abs_of_pos hh] at ht
    apply (div_le_iff₀ hp).mpr
    change hi-lo ≤ R*(hi+lo)
    nlinarith [mul_le_mul_of_nonneg_left ha hh.le,mul_le_mul_of_nonneg_left hb hl.le]
  refine ⟨le_antisymm ?_ (lower _),lower⟩
  rw [herm_res_norm hY]
  apply (pi_norm_le_iff_of_nonneg hn).mpr
  intro t
  change ‖(1:ℂ)-((2/(lo+hi):ℝ):ℂ)*(hY.eigenvalues t:ℂ)‖ ≤ _
  rw [←Complex.ofReal_mul,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have h1 := (hall t).1
  have h2 := (hall t).2
  rw [add_comm hi lo,abs_le]
  constructor
  · field_simp; linarith
  · field_simp; linarith

end OMA.S_mo_271853

namespace OMA.S_mo_271853
open Matrix Finset
open scoped Matrix.Norms.L2Operator

private lemma coef_diagonal {n : ℕ} (d : Fin n → ℂ) :
    coef (1 : Mat n n) (diagonal d) = (∑ i, star (d i)) / ((∑ i, ‖d i‖^2 : ℝ) : ℂ) := by
  simp [coef, Matrix.one_apply, Matrix.diagonal_apply, apply_ite, eq_comm]

lemma sharp (n : ℕ) (hn : 2 ≤ n) : ∃ Y : Mat n n,
    (∀ z : ℂ, 1 ≤ ‖1-z•Y‖) ∧ ‖(1:Mat n n)-coef 1 Y • Y‖=(1+Real.sqrt n)/2 := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+2 := ⟨n-2,by omega⟩
  let r : ℝ := Real.sqrt (m+2)
  have hr : r^2 = (m:ℝ)+2 := Real.sq_sqrt (by positivity)
  have hrr : 1 < r := by nlinarith [show 0≤r from Real.sqrt_nonneg _]
  let d : Fin (m+2) → ℂ := Fin.cases ((r-1:ℝ):ℂ) (fun _ => -1)
  have hc : coef (1:Mat (m+2) (m+2)) (diagonal d) = ((-1/2:ℝ):ℂ) := by
    rw [coef_diagonal]
    have hnum : (∑ i, star (d i)) = (((r-1)-(m+1):ℝ):ℂ) := by
      rw [Fin.sum_univ_succ]
      simp [d]; ring
    have hden : (∑ i, ‖d i‖^2) = (r-1)^2+((m:ℝ)+1) := by
      rw [Fin.sum_univ_succ]
      simp [d]
      rw [←Complex.ofReal_one,←Complex.ofReal_sub]
      simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rw [hnum,hden,←Complex.ofReal_div]
    apply congrArg Complex.ofReal
    apply (div_eq_iff (by positivity : (r-1)^2+((m:ℝ)+1)≠0)).mpr
    nlinarith
  refine ⟨diagonal d,?_,?_⟩
  · intro z
    rw [diag_res_norm]
    let v : Fin (m+2) → ℂ := fun i => 1-z*d i
    change 1 ≤ ‖v‖
    by_cases hz : 0 ≤ z.re
    · have h := Complex.re_le_norm (v (Fin.succ 0))
      have hv : (v (Fin.succ 0)).re = 1 + z.re := by change (1-z*(-1)).re = 1+z.re; simp
      exact (show 1 ≤ ‖v (Fin.succ 0)‖ by linarith).trans (norm_le_pi_norm v _)
    · have h := Complex.re_le_norm (v 0)
      have hv : (v 0).re = 1 - z.re*(r-1) := by simp [v,d]
      have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hz) (sub_nonneg.mpr hrr.le)
      exact (show 1 ≤ ‖v 0‖ by linarith).trans (norm_le_pi_norm v _)
  · rw [hc,diag_res_norm]
    push_cast
    change ‖fun i => (1:ℂ) - (-1/2)*d i‖ = (1+r)/2
    have hzero : ‖(1:ℂ) - (-1/2)*d 0‖ = (1+r)/2 := by
      have he : (1:ℂ) - (-1/2)*d 0 = (((1+r)/2:ℝ):ℂ) := by simp [d]; ring
      rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by linarith : 0≤(1+r)/2)).mpr
      intro i
      refine Fin.cases hzero.le (fun j => ?_) i
      change ‖(1:ℂ)-(-1/2)*d j.succ‖ ≤ _
      have he : (1:ℂ)-(-1/2)*d j.succ = ((1/2:ℝ):ℂ) := by simp [d]; ring
      rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by norm_num)]
      linarith
    · rw [←hzero]
      exact norm_le_pi_norm (fun i => (1:ℂ) - (-1/2)*d i) 0

end OMA.S_mo_271853

open OMA.S_mo_271853

theorem OMA.solution : type_of% @OMA.S_mo_271853.main :=
  ⟨fun _ _ X Y z t ht => sdp (X-z•Y) t ht,fun _ _ hm hn => loss hm hn,sharp,positive_case⟩
