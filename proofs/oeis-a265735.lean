import OMAStatements.S_oeis_a265735

open OMA.S_oeis_a265735 in
theorem OMA.solution : type_of% @OMA.S_oeis_a265735.main := by
  intro hT
  have hS := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational irrational_pi
  obtain ⟨B, hB⟩ := hT.bddAbove
  have key : ∀ q : ℚ, |Real.pi - q| < 1 / (q.den : ℝ) ^ 2 →
      q.num ∈ {m : ℤ | IsTerm m} ∧ (q.den : ℤ) < q.num := by
    intro q hq
    have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hd1 : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
    have hqq : (q : ℝ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
    have e : |Real.pi * q.den - q.num| = |Real.pi - q| * q.den := by
      rw [hqq, ← abs_of_pos hd, ← abs_mul, abs_of_pos hd]; congr 1; field_simp
    have h2 : |Real.pi * q.den - q.num| < 1 / q.den := by
      rw [e]; calc |Real.pi - q| * q.den < 1 / (q.den : ℝ) ^ 2 * q.den := by gcongr
        _ = 1 / q.den := by field_simp
    refine ⟨⟨q.den, q.den_pos, h2.le⟩, ?_⟩
    have h3 := (abs_lt.mp h2).2
    have h4 : 1 / (q.den : ℝ) ≤ 1 := by rw [div_le_one hd]; exact hd1
    have := Real.pi_gt_three
    have : (q.den : ℝ) < q.num := by nlinarith
    exact_mod_cast this
  apply hS
  apply Set.Finite.of_finite_image (f := fun q : ℚ => (q.num, q.den))
  · apply Set.Finite.subset ((Set.finite_Icc (-1 : ℤ) B).prod (Set.finite_Iic B.toNat))
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨h1, h2⟩ := key q hq
    have h5 := hB h1
    have : (0:ℤ) < q.den := by exact_mod_cast q.den_pos
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Iic]
    refine ⟨⟨by omega, h5⟩, by omega⟩
  · intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    exact Rat.ext h.1 h.2
