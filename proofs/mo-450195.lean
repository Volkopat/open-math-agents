import OMAStatements.S_mo_450195
import Mathlib

-- Problem: mo-450195, for a fixed nonnegative integer matrix M, is there (R, eps) such that
-- every nonnegative integer vector b with an eps-approximate real solution of M x = b has an
-- exact real solution?
-- Credit: @ivillar, original proof #25781 and statement #20101.
-- Denominator-clearing simplification by @rodolfoquint using Mathlib localization APIs.
--
-- Yes (with R = 0). Over the rationals, compose the quotient map by the column space W of M
-- with coordinates on the quotient: this is a linear map P with kernel W. The finite-family localization theorem clears denominators
-- in the matrix of P and gives integer vectors z_k with z_k . M = 0 such that a rational vector v
-- lies in W as soon as z_k . v = 0 for all k. If |M x' - b| < eps = 1 / (Z + 1), where Z is the
-- sum of all |z_{k,i}|, then the integer z_k . b = z_k . (b - M x') has absolute value < 1, so
-- it is 0. Hence b = M y for a rational y.

namespace MO450195

theorem alg (m n : ℕ) (Mq : Matrix (Fin m) (Fin n) ℚ) :
    ∃ (r : ℕ) (z : Fin r → Fin m → ℤ),
      (∀ k j, ∑ i, (z k i : ℚ) * Mq i j = 0) ∧
      ∀ v : Fin m → ℚ, (∀ k, ∑ i, (z k i : ℚ) * v i = 0) →
        ∃ y : Fin n → ℚ, Mq.mulVec y = v := by
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℚ (Fin m → ℚ), W = LinearMap.range Mq.mulVecLin :=
    ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : (Fin m → ℚ) →ₗ[ℚ]
      (Fin (Module.finrank ℚ ((Fin m → ℚ) ⧸ W)) → ℚ), ∀ v, P v = 0 ↔ v ∈ W := by
    refine ⟨(Module.finBasis ℚ ((Fin m → ℚ) ⧸ W)).equivFun.toLinearMap ∘ₗ W.mkQ, ?_⟩
    intro v
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℚ ((Fin m → ℚ) ⧸ W)) → Fin m → ℚ,
      ∀ k i, c k i = P (fun j => if i = j then 1 else 0) k := ⟨_, fun _ _ => rfl⟩
  have hPc : ∀ (v : Fin m → ℚ) k, P v k = ∑ i, v i * c k i := by
    intro v k
    rw [LinearMap.pi_apply_eq_sum_univ P v, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, hc]
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun i : Fin (Module.finrank ℚ ((Fin m → ℚ) ⧸ W)) × Fin m => c i.1 i.2)
  have hN0 : (N.val : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.ne_zero N.property
  have hz : ∀ k i, ∃ t : ℤ, (t : ℚ) = c k i * N.val := by
    intro k i
    simpa [IsLocalization.IsInteger, Algebra.smul_def, mul_comm] using hN (k, i)
  choose z hz using hz
  have hsum : ∀ k (x : Fin m → ℚ), ∑ i, (z k i : ℚ) * x i = (N.val : ℚ) * P x k := by
    intro k x
    rw [hPc, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hz]
    ring
  refine ⟨_, z, ?_, ?_⟩
  · intro k j
    have h0 : P (fun i => Mq i j) = 0 := by
      rw [hP, hW]
      refine ⟨Pi.single j 1, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
      rfl
    have h1 := hsum k (fun i => Mq i j)
    rw [h0] at h1
    simpa using h1
  · intro v hv
    have hPv : P v = 0 := by
      funext k
      have h1 := hsum k v
      rw [hv k] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left hN0
    have hmem := (hP v).mp hPv
    rw [hW] at hmem
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, by rw [← hy, Matrix.mulVecLin_apply]⟩

theorem ana (m n r : ℕ) (M : Matrix (Fin m) (Fin n) ℕ) (z : Fin r → Fin m → ℤ)
    (hI : ∀ k j, ∑ i, z k i * (M i j : ℤ) = 0) (b : Fin m → ℕ) (x' : Fin n → ℝ)
    (hx : ‖(M.map (fun a : ℕ => (a : ℝ))).mulVec x' - (fun i => (b i : ℝ))‖ <
      1 / ((∑ k, ∑ i, |(z k i : ℝ)|) + 1)) (k : Fin r) :
    ∑ i, z k i * (b i : ℤ) = 0 := by
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ∑ k, ∑ i, |(z k i : ℝ)| := ⟨_, rfl⟩
  rw [← hZ] at hx
  have hZ0 : 0 ≤ Z := by
    rw [hZ]
    exact Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  obtain ⟨w, hw⟩ : ∃ w : Fin m → ℝ, w = (M.map (fun a : ℕ => (a : ℝ))).mulVec x' := ⟨_, rfl⟩
  rw [← hw] at hx
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ‖w - fun i => (b i : ℝ)‖ := ⟨_, rfl⟩
  rw [← hη] at hx
  have hη0 : 0 ≤ η := by
    rw [hη]
    exact norm_nonneg _
  have hδ : ∀ i, |(b i : ℝ) - w i| ≤ η := by
    intro i
    have h := norm_le_pi_norm (w - fun i => (b i : ℝ)) i
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm, ← hη] at h
    exact h
  have h0 : ∑ i, (z k i : ℝ) * w i = 0 := by
    rw [hw]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have hr : ∑ i, (z k i : ℝ) * (M i j : ℝ) = 0 := by
      exact_mod_cast hI k j
    calc ∑ i, (z k i : ℝ) * ((M i j : ℝ) * x' j)
        = (∑ i, (z k i : ℝ) * (M i j : ℝ)) * x' j := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = 0 := by rw [hr, zero_mul]
  have hT : ((∑ i, z k i * (b i : ℤ) : ℤ) : ℝ) = ∑ i, (z k i : ℝ) * ((b i : ℝ) - w i) := by
    have e : ∑ i, (z k i : ℝ) * ((b i : ℝ) - w i) =
        ∑ i, (z k i : ℝ) * (b i : ℝ) - ∑ i, (z k i : ℝ) * w i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, h0, sub_zero]
    push_cast
    rfl
  have hrow : ∑ i, |(z k i : ℝ)| ≤ Z := by
    rw [hZ]
    exact Finset.single_le_sum (f := fun k => ∑ i, |(z k i : ℝ)|)
      (fun k _ => Finset.sum_nonneg (fun i _ => abs_nonneg _)) (Finset.mem_univ k)
  have hb1 : |∑ i, (z k i : ℝ) * ((b i : ℝ) - w i)| ≤ (∑ i, |(z k i : ℝ)|) * η := by
    calc |∑ i, (z k i : ℝ) * ((b i : ℝ) - w i)|
        ≤ ∑ i, |(z k i : ℝ) * ((b i : ℝ) - w i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |(z k i : ℝ)| * η := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hδ i) (abs_nonneg _)
      _ = (∑ i, |(z k i : ℝ)|) * η := by rw [Finset.sum_mul]
  have hpos : 0 < Z + 1 := by linarith
  have hlt : (Z + 1) * η < 1 := by
    have h := (lt_div_iff₀ hpos).mp hx
    linarith
  have hb2 : |((∑ i, z k i * (b i : ℤ) : ℤ) : ℝ)| < 1 := by
    rw [hT]
    have h3 : (∑ i, |(z k i : ℝ)|) * η ≤ Z * η := mul_le_mul_of_nonneg_right hrow hη0
    nlinarith
  have hb3 : |∑ i, z k i * (b i : ℤ)| < 1 := by
    exact_mod_cast hb2
  have hb4 := abs_lt.mp hb3
  omega

end MO450195

theorem OMA.solution : type_of% @OMA.S_mo_450195.main := by
  intro m n _ M
  obtain ⟨r, z, hI, hII⟩ := MO450195.alg m n (M.map (fun a : ℕ => (a : ℚ)))
  have hI' : ∀ k j, ∑ i, z k i * (M i j : ℤ) = 0 := by
    intro k j
    have h := hI k j
    simp only [Matrix.map_apply] at h
    exact_mod_cast h
  refine ⟨0, 1 / ((∑ k, ∑ i, |(z k i : ℝ)|) + 1), ?_, ?_⟩
  · have hZ0 : 0 ≤ ∑ k, ∑ i, |(z k i : ℝ)| :=
      Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
    positivity
  · intro b _ x' hx'
    have hT := MO450195.ana m n r M z hI' b x' hx'
    obtain ⟨y, hy⟩ := hII (fun i => (b i : ℚ)) (fun k => by
      have h := hT k
      exact_mod_cast h)
    refine ⟨fun j => (y j : ℝ), ?_⟩
    funext i
    have hi := congrFun hy i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hi ⊢
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hi
