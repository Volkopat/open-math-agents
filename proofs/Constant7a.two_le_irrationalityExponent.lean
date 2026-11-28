import FormalConjectures.OptimizationConstants.«7a»

/-! A denominator bound also bounds the numerators of the Dirichlet approximants.
They are infinitely many, so their denominators are unbounded. -/

open Filter Set

theorem OMA.solution : type_of% @Constant7a.two_le_irrationalityExponent := by
  intro x hx
  suffices h : LiouvilleWith 2 x by
    exact le_sSup ⟨(2 : NNReal), by simpa using h, by norm_num⟩
  refine ⟨1, frequently_atTop.mpr fun N => ?_⟩
  let S : Set ℚ := {q | |x - (q : ℝ)| < 1 / (q.den : ℝ)^2}
  obtain ⟨C, hC⟩ := exists_int_ge ((|x| + 1) * (N : ℝ))
  have fin : {q ∈ S | q.den ≤ N}.Finite := by
    refine Finite.of_injOn (f := fun q => (q.num, q.den)) ?_ ?_
      ((finite_Icc (a := -C) (b := C)).prod (finite_Iic N))
    · rintro q ⟨hq, hn⟩
      have h₁ : |(q : ℝ)| - |x| ≤ |x - (q : ℝ)| := by
        rw [abs_sub_comm x]
        exact abs_sub_abs_le_abs_sub ..
      have h₂ : |x - (q : ℝ)| ≤ 1 := hq.le.trans <| (div_le_one (by positivity)).mpr
        (by exact_mod_cast Nat.one_le_pow 2 _ q.den_pos)
      have h₃ : |(q.num : ℝ)| = |(q : ℝ)| * q.den := by
        rw [Rat.cast_def, abs_div, Nat.abs_cast, div_mul_cancel₀ _ (by positivity)]
      have hh := mul_le_mul (show |(q : ℝ)| ≤ |x|+1 by linarith) (Nat.cast_le.mpr hn)
        (Nat.cast_nonneg _) (by positivity)
      exact ⟨by exact_mod_cast abs_le.mp (h₃.trans_le (hh.trans hC)), hn⟩
    · intro a _ b _ e
      exact Rat.ext (Prod.mk.inj e).1 (Prod.mk.inj e).2
  obtain ⟨q, hq, hl⟩ := (Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx).exists_notMem_finite fin
  refine ⟨q.den, le_of_not_ge (fun h => hl ⟨hq,h⟩), q.num, ?_, ?_⟩
  · rw [← Rat.cast_def]
    exact hx.ne_rat q
  · rw [← Rat.cast_def, Real.rpow_two]
    exact hq
