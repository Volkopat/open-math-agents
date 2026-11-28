import OMAStatements.S_arxiv_2007_02618
import Mathlib

namespace OMA.P_arxiv_2007_02618

open OMA.S_arxiv_2007_02618

/-- Strictly positive `3 × 3` counterexample matrix (Altenberg–Cohen perturbation, scaled by 100):
`A = [[1, 100, 1], [1, 1, 1], [1, 1, 40]]`. -/
def A0 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    match i.val, j.val with
    | 0, 1 => 100
    | 2, 2 => 40
    | _, _ => 1

def B0 (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 - t) • A0 + t • A0.transpose

lemma A0_nonnegIrred : IsNonnegIrreducible A0 := by
  constructor
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [A0]
  · intro i j; refine ⟨1, Nat.one_pos, ?_⟩
    rw [pow_one]
    fin_cases i <;> fin_cases j <;> norm_num [A0]

private lemma rootSet_bddAbove {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    BddAbove { r : ℝ | ∃ μ : ℂ, (M.charpoly.map (algebraMap ℝ ℂ)).IsRoot μ ∧ ‖μ‖ = r } := by
  have hne : M.charpoly.map (algebraMap ℝ ℂ) ≠ 0 := by
    have hm : (M.charpoly.map (algebraMap ℝ ℂ)).Monic := M.charpoly_monic.map _
    exact hm.ne_zero
  have hfin : { r : ℝ | ∃ μ : ℂ, (M.charpoly.map (algebraMap ℝ ℂ)).IsRoot μ ∧ ‖μ‖ = r }.Finite := by
    have hroots : { μ : ℂ | (M.charpoly.map (algebraMap ℝ ℂ)).IsRoot μ }.Finite :=
      (M.charpoly.map (algebraMap ℝ ℂ)).roots.toFinset.finite_toSet.subset fun μ hμ => by
        rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne]
        exact hμ
    exact (hroots.image (fun μ : ℂ => ‖μ‖)).subset fun r hr => by
      obtain ⟨μ, hμ, rfl⟩ := hr
      exact ⟨μ, hμ, rfl⟩
  exact hfin.bddAbove

private lemma eval_charpoly_eq_det {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) (x : R) :
    M.charpoly.eval x = (Matrix.scalar (Fin 3) x - M).det := by
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.charmatrix, Matrix.sub_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply, Polynomial.coe_evalRingHom,
    Polynomial.eval_sub, Polynomial.eval_C]
  split_ifs <;> simp

private lemma det_3x3_formula (X : Matrix (Fin 3) (Fin 3) ℝ) :
    X.det =
      X 0 0 * (X 1 1 * X 2 2 - X 1 2 * X 2 1) -
      X 0 1 * (X 1 0 * X 2 2 - X 1 2 * X 2 0) +
      X 0 2 * (X 1 0 * X 2 1 - X 1 1 * X 2 0) := by
  rw [Matrix.det_fin_three]
  ring

private lemma charpoly_B0_eval (t x : ℝ) :
    (B0 t).charpoly.eval x =
      x ^ 3 - 42 * x ^ 2 + (9801 * t ^ 2 - 9801 * t - 21) * x +
      (3861 + 392040 * t - 392040 * t ^ 2) := by
  have h00 : A0 0 0 = 1 := rfl
  have h01 : A0 0 1 = 100 := rfl
  have h02 : A0 0 2 = 1 := rfl
  have h10 : A0 1 0 = 1 := rfl
  have h11 : A0 1 1 = 1 := rfl
  have h12 : A0 1 2 = 1 := rfl
  have h20 : A0 2 0 = 1 := rfl
  have h21 : A0 2 1 = 1 := rfl
  have h22 : A0 2 2 = 40 := rfl
  rw [eval_charpoly_eq_det, det_3x3_formula]
  simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    B0, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
    h00, h01, h02, h10, h11, h12, h20, h21, h22,
    show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    ↓reduceIte]
  ring

private lemma le_spectralRadius_of_real_root {M : Matrix (Fin 3) (Fin 3) ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hroot : M.charpoly.eval r = 0) :
    r ≤ spectralRadius M := by
  apply le_csSup (rootSet_bddAbove M)
  refine ⟨(r : ℂ), ?_, ?_⟩
  · change (M.charpoly.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = 0
    rw [Polynomial.eval_map_apply, hroot, map_zero]
  · simp [Complex.norm_real, abs_of_nonneg hr]

private lemma exists_real_root_ge {M : Matrix (Fin 3) (Fin 3) ℝ} {a b : ℝ}
    (hab : a ≤ b) (ha : M.charpoly.eval a ≤ 0) (hb : 0 ≤ M.charpoly.eval b) :
    ∃ r ∈ Set.Icc a b, M.charpoly.eval r = 0 := by
  have hcont : ContinuousOn (fun x => M.charpoly.eval x) (Set.Icc a b) :=
    M.charpoly.continuous.continuousOn
  exact intermediate_value_Icc hab hcont ⟨ha, hb⟩

lemma spectralRadius_B0_01_ge : (403 / 10 : ℝ) ≤ spectralRadius (B0 (1 / 10)) := by
  have ha : (B0 (1 / 10)).charpoly.eval (403 / 10) ≤ 0 := by
    rw [charpoly_B0_eval]; norm_num
  have hb : 0 ≤ (B0 (1 / 10)).charpoly.eval 60 := by
    rw [charpoly_B0_eval]; norm_num
  obtain ⟨r, ⟨hr1, _⟩, hroot⟩ := exists_real_root_ge (by norm_num : (403 / 10 : ℝ) ≤ 60) ha hb
  exact le_trans hr1 (le_spectralRadius_of_real_root (by linarith) hroot)

lemma spectralRadius_B0_03_ge : (477 / 10 : ℝ) ≤ spectralRadius (B0 (3 / 10)) := by
  have ha : (B0 (3 / 10)).charpoly.eval (477 / 10) ≤ 0 := by
    rw [charpoly_B0_eval]; norm_num
  have hb : 0 ≤ (B0 (3 / 10)).charpoly.eval 60 := by
    rw [charpoly_B0_eval]; norm_num
  obtain ⟨r, ⟨hr1, _⟩, hroot⟩ := exists_real_root_ge (by norm_num : (477 / 10 : ℝ) ≤ 60) ha hb
  exact le_trans hr1 (le_spectralRadius_of_real_root (by linarith) hroot)

/-- Collatz–Wielandt upper bound: for any nonnegative `3 × 3` matrix `M`, any strictly positive
vector `v : Fin 3 → ℝ`, and `c : ℝ`, if `(M *ᵥ v) i ≤ c * v i` for all `i`, then every complex
root `μ` of `M.charpoly` satisfies `‖μ‖ ≤ c`. -/
private lemma norm_root_le_of_pos_vec (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (v : Fin 3 → ℝ) (hv : ∀ i, 0 < v i) (c : ℝ)
    (hMv : ∀ i, (∑ j : Fin 3, M i j * v j) ≤ c * v i)
    {μ : ℂ} (hμ : (M.charpoly.map (algebraMap ℝ ℂ)).IsRoot μ) :
    ‖μ‖ ≤ c := by
  let MC : Matrix (Fin 3) (Fin 3) ℂ := M.map (algebraMap ℝ ℂ)
  have hdet : (Matrix.scalar (Fin 3) μ - MC).det = 0 := by
    rw [← eval_charpoly_eq_det]
    have hcm : MC.charpoly = M.charpoly.map (algebraMap ℝ ℂ) := by
      rw [Matrix.charpoly, Matrix.charpoly, ← Polynomial.coe_mapRingHom, RingHom.map_det]
      congr 1; ext i j
      simp only [MC, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.charmatrix,
        Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
        Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_C]
      split_ifs <;> simp
    rw [hcm]
    exact hμ
  obtain ⟨w, hw_ne, hAw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hmul : ∀ i : Fin 3, (∑ j : Fin 3, (M i j : ℂ) * w j) = μ * w i := by
    intro i
    have hi := congrFun hAw i
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at hi
    have : μ * w i = ∑ j : Fin 3, MC i j * w j := sub_eq_zero.mp hi
    exact this.symm
  -- Pick `i0` maximizing `‖w i‖ / v i`
  have hex : ∃ i0 : Fin 3, ∀ j : Fin 3, ‖w j‖ / v j ≤ ‖w i0‖ / v i0 := by
    obtain ⟨i0, _, hi0⟩ := Finset.exists_max_image Finset.univ (fun i : Fin 3 => ‖w i‖ / v i)
      ⟨0, Finset.mem_univ 0⟩
    exact ⟨i0, fun j => hi0 j (Finset.mem_univ j)⟩
  obtain ⟨i0, hi0⟩ := hex
  have hwi0_pos : 0 < ‖w i0‖ := by
    by_contra hle
    have hle' : ‖w i0‖ ≤ 0 := le_of_not_gt hle
    have h0 : ‖w i0‖ = 0 := le_antisymm hle' (norm_nonneg _)
    apply hw_ne
    funext j
    have hj := hi0 j
    rw [h0, zero_div] at hj
    have hj0 : ‖w j‖ ≤ 0 := by
      have := mul_le_mul_of_nonneg_right hj (le_of_lt (hv j))
      rwa [div_mul_cancel₀ _ (ne_of_gt (hv j)), zero_mul] at this
    exact norm_eq_zero.mp (le_antisymm hj0 (norm_nonneg _))
  have hbound : ‖μ‖ * ‖w i0‖ ≤ c * ‖w i0‖ := by
    calc ‖μ‖ * ‖w i0‖
        = ‖μ * w i0‖ := (norm_mul μ (w i0)).symm
      _ = ‖∑ j : Fin 3, (M i0 j : ℂ) * w j‖ := by rw [hmul i0]
      _ ≤ ∑ j : Fin 3, ‖(M i0 j : ℂ) * w j‖ := norm_sum_le _ _
      _ = ∑ j : Fin 3, M i0 j * ‖w j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hM i0 j)]
      _ ≤ ∑ j : Fin 3, M i0 j * ((‖w i0‖ / v i0) * v j) := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hM i0 j)
          have := mul_le_mul_of_nonneg_right (hi0 j) (le_of_lt (hv j))
          rwa [div_mul_cancel₀ _ (ne_of_gt (hv j))] at this
      _ = (‖w i0‖ / v i0) * ∑ j : Fin 3, M i0 j * v j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ (‖w i0‖ / v i0) * (c * v i0) :=
          mul_le_mul_of_nonneg_left (hMv i0) (div_nonneg (norm_nonneg _) (le_of_lt (hv i0)))
      _ = c * ‖w i0‖ := by
          field_simp [ne_of_gt (hv i0)]
  exact le_of_mul_le_mul_right hbound hwi0_pos

lemma spectralRadius_B0_02_le : spectralRadius (B0 (2 / 10)) ≤ (436 / 10 : ℝ) := by
  have hne : { r : ℝ | ∃ μ : ℂ, ((B0 (2 / 10)).charpoly.map (algebraMap ℝ ℂ)).IsRoot μ ∧ ‖μ‖ = r }.Nonempty := by
    have ha : (B0 (2 / 10)).charpoly.eval 40 ≤ 0 := by rw [charpoly_B0_eval]; norm_num
    have hb : 0 ≤ (B0 (2 / 10)).charpoly.eval 60 := by rw [charpoly_B0_eval]; norm_num
    obtain ⟨r, _, hroot⟩ := exists_real_root_ge (by norm_num : (40 : ℝ) ≤ 60) ha hb
    refine ⟨‖(r : ℂ)‖, (r : ℂ), ?_, rfl⟩
    change ((B0 (2 / 10)).charpoly.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = 0
    rw [Polynomial.eval_map_apply, hroot, map_zero]
  apply csSup_le hne
  rintro r ⟨μ, hμ, rfl⟩
  let v : Fin 3 → ℝ := fun i => if i = 0 then 2 else 1
  refine norm_root_le_of_pos_vec (B0 (2 / 10)) ?_ v ?_ (436 / 10) ?_ hμ
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [B0, A0, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
        Matrix.of_apply] <;>
      norm_num
  · intro i; fin_cases i <;> simp [v]
  · intro i
    fin_cases i <;>
      simp only [Fin.sum_univ_three, B0, A0, v, Matrix.add_apply, Matrix.smul_apply,
        Matrix.transpose_apply, smul_eq_mul, Matrix.of_apply, Fin.isValue,
        show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte] <;>
      norm_num

end OMA.P_arxiv_2007_02618

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2007_02618.main) := by
  intro h
  have hconc := h 3 (by norm_num) OMA.P_arxiv_2007_02618.A0 OMA.P_arxiv_2007_02618.A0_nonnegIrred
  have hmid := hconc.2
    (show (1 / 10 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by norm_num)
    (show (3 / 10 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have ht : (1 / 2 : ℝ) • (1 / 10 : ℝ) + (1 / 2 : ℝ) • (3 / 10 : ℝ) = 2 / 10 := by norm_num
  rw [ht] at hmid
  simp only [smul_eq_mul] at hmid
  have h1 := OMA.P_arxiv_2007_02618.spectralRadius_B0_01_ge
  have h2 := OMA.P_arxiv_2007_02618.spectralRadius_B0_03_ge
  have hm := OMA.P_arxiv_2007_02618.spectralRadius_B0_02_le
  change (1 / 2 : ℝ) * OMA.S_arxiv_2007_02618.spectralRadius (OMA.P_arxiv_2007_02618.B0 (1 / 10)) +
    (1 / 2 : ℝ) * OMA.S_arxiv_2007_02618.spectralRadius (OMA.P_arxiv_2007_02618.B0 (3 / 10)) ≤
    OMA.S_arxiv_2007_02618.spectralRadius (OMA.P_arxiv_2007_02618.B0 (2 / 10)) at hmid
  linarith
