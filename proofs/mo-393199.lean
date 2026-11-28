import OMAStatements.S_mo_393199

/-! Credit: @Genbox for the original perturbation counterexample. -/

open OMA.S_mo_393199 Matrix Polynomial

private abbrev M₂ := Matrix (Fin 2) (Fin 2) ℝ

private def A : M₂ := !![-2, 3; -2, 3]

private def C₀ : M₂ := Matrix.diagonal fun i => if i = 0 then 1 else 0

private theorem perturbation_eval (e t : ℝ) (ht : t ≠ 0) :
    (block A 0 C₀ e).charpoly.eval t =
      t ^ 2 * ((t + e + 2 + t⁻¹ * e) * (t + e - 3) + 6) := by
  let I : M₂ := 1
  let D : M₂ := t • I
  have hblocks : Matrix.scalar (Fin 2 ⊕ Fin 2) t - block A 0 C₀ e =
      fromBlocks ((t + e) • I - A) (-I) (e • C₀) D := by
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    ext i j
    rcases i with i | i <;> rcases j with j | j
    all_goals simp [block, I, D, smul_eq_mul]
    ring
  let : Invertible D :=
    ⟨t⁻¹ • I, by simp [D, I, ht],
      by simp [D, I, ht]⟩
  have hInv : ⅟D = t⁻¹ • I := rfl
  have hdetD : D.det = t ^ 2 := by simp [D, I]
  have hproduct : (-I) * (t⁻¹ • I) * (e • C₀) = -((t⁻¹ * e) • C₀) := by
    simp [I, smul_smul, mul_comm]
  rw [Matrix.eval_charpoly, hblocks, Matrix.det_fromBlocks₂₂, hInv, hproduct,
    hdetD, sub_neg_eq_add, Matrix.det_fin_two]
  norm_num [A, C₀, I, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul]

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_393199.main) := by
  intro h
  have hApoly : A.charpoly = X * (X - Polynomial.C 1) := by
    rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    norm_num [A]
    ring
  have hsimple : A.charpoly.rootMultiplicity 1 = 1 := by
    rw [hApoly, ← pow_one (X - Polynomial.C (1 : ℝ)),
      Polynomial.rootMultiplicity_mul_X_sub_C_pow Polynomial.X_ne_zero,
      Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot])]
  have hAstable (z : ℂ) (hz : Polynomial.aeval z A.charpoly = 0) (hz1 : z ≠ 1) :
      ‖z‖ < 1 := by
    rw [hApoly] at hz
    simp only [map_mul, map_sub, Polynomial.aeval_X, map_one] at hz
    obtain hz | hz := mul_eq_zero.mp hz
    · simp [hz]
    · exact (hz1 (sub_eq_zero.mp hz)).elim
  have hBstable : stable (0 : M₂) := by
    intro z hz
    rw [Matrix.charpoly_fin_two] at hz
    simp at hz
    simp [hz]
  have hCpos : C₀.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> norm_num
  obtain ⟨δ, hδ, hstable⟩ := h 2 A 0 C₀ hsimple hAstable hBstable hCpos (Commute.zero_left _)
  let e := min (δ / 2) (1 / 4)
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have heδ : e < δ := (min_le_left _ _).trans_lt (by linarith)
  have he₄ : e ≤ 1 / 4 := min_le_right _ _
  specialize hstable e ⟨he, heδ⟩
  let p := (block A 0 C₀ e).charpoly
  have hp₁ : p.eval 1 < 0 := by
    change (block A 0 C₀ e).charpoly.eval 1 < 0
    rw [perturbation_eval e 1 one_ne_zero]
    norm_num
    nlinarith [mul_pos he (show 0 < 1 - 2 * e by linarith)]
  have hp₂ : 0 < p.eval 2 := by
    change 0 < (block A 0 C₀ e).charpoly.eval 2
    rw [perturbation_eval e 2 (by norm_num)]
    norm_num
    nlinarith [sq_nonneg e]
  obtain ⟨t, ht, hp⟩ :=
    intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) p.continuous.continuousOn
      (show 0 ∈ Set.Icc (p.eval 1) (p.eval 2) from ⟨hp₁.le, hp₂.le⟩)
  have htt : 1 ≤ t := ht.1
  change p.eval t = 0 at hp
  have hroot : Polynomial.aeval (t : ℂ) p = 0 := by
    rw [show (t : ℂ) = algebraMap ℝ ℂ t from rfl,
      Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hp, map_zero]
  have hnorm := hstable (t : ℂ) hroot
  rw [Complex.norm_of_nonneg (by linarith : 0 ≤ t)] at hnorm
  linarith