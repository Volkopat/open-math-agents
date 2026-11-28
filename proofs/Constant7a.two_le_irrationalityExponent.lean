import FormalConjectures.OptimizationConstants.«7a»

/-! Unbounded denominators among Dirichlet approximants give irrationality exponent at least two. -/

open Filter Set

theorem OMA.solution : type_of% @Constant7a.two_le_irrationalityExponent := by
  intro x hx
  suffices h : LiouvilleWith 2 x from le_sSup ⟨2, by simpa using h, by norm_num⟩
  refine ⟨1, frequently_atTop.mpr fun N => ?_⟩
  obtain ⟨C, hC⟩ := exists_int_ge ((|x| + 1) * N)
  have fin : {q : ℚ | |x - q| < 1 / (q.den : ℝ) ^ 2 ∧ q.den ≤ N}.Finite := by
    refine Finite.of_injOn (f := fun q => (q.num, q.den)) ?_
      (fun a _ b _ e => Rat.ext (Prod.mk.inj e).1 (Prod.mk.inj e).2)
      ((finite_Icc (-C) C).prod (finite_Iic N))
    rintro q ⟨hq, hn⟩
    have h1 : |x - q| ≤ 1 := hq.le.trans <| (div_le_one (by positivity)).mpr
      (by exact_mod_cast Nat.one_le_pow 2 _ q.den_pos)
    have h2 : |(q : ℝ)| ≤ |x| + 1 := by
      linarith [abs_sub_abs_le_abs_sub (q : ℝ) x, abs_sub_comm x (q : ℝ)]
    have hd : (0 : ℝ) < q.den := by positivity
    refine ⟨abs_le.mp ?_, hn⟩
    exact_mod_cast (show |(q.num : ℝ)| ≤ C by
      rw [← div_mul_cancel₀ (q.num : ℝ) hd.ne', ← Rat.cast_def, abs_mul, abs_of_pos hd]
      nlinarith [abs_nonneg (q : ℝ), show (q.den : ℝ) ≤ N by exact_mod_cast hn])
  obtain ⟨q, hq, hl⟩ :=
    (Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx).exists_notMem_finite fin
  refine ⟨q.den, le_of_not_ge fun h => hl ⟨hq, h⟩, q.num, ?_, ?_⟩
  · rw [← Rat.cast_def]; exact hx.ne_rat q
  · rwa [← Rat.cast_def, Real.rpow_two]
