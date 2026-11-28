import OMAStatements.S_oeis_a343913

-- Credit: @CubeJerry
-- Write x = d + y. The Pell transformation sends (d,y) to
-- (17d + 12y, 7d + 5y), preserving 7d² + 17 = 12y(d+y).
-- The second invariant keeps the square root integral as d grows.

private theorem unbounded_triples (B : ℕ) :
    ∃ d y m : ℕ, B < m ∧ 1 < d ∧
      7 * (d : ℤ)^2 + 17 = 12 * y * (d + y : ℤ) ∧
      12 * (m : ℤ) = 17 * (d : ℤ)^2 + 19 := by
  induction B with
  | zero =>
    exact ⟨29, 12, 1193, by decide, by decide, by decide, by decide⟩
  | succ B ih =>
    obtain ⟨d, y, m, hB, hd, hconic, hroot⟩ := ih
    refine ⟨17*d + 12*y, 7*d + 5*y, m + 34*(12*d^2 + 17*d*y + 6*y^2),
      ?_, by omega, ?_, ?_⟩
    · have hpos : 0 < 12*d^2 := by positivity
      omega
    · push_cast
      linear_combination hconic
    · push_cast
      linear_combination hroot

theorem OMA.solution : type_of% @OMA.S_oeis_a343913.main := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨d, y, m, hB, hd, hconic, hroot⟩ := unbounded_triples B
  refine ⟨m, ⟨by omega, d+y, y, ?_, ?_⟩, hB⟩
  · push_cast
    have h : 144 * (((d : ℤ) + y)^4 + (y : ℤ)^4) =
        144 * (d : ℤ)^4 + 48*d^2*(12*y*(d+y : ℤ)) + 2*(12*y*(d+y : ℤ))^2 := by
      linear_combination
    rw [← hconic] at h
    have hs := congrArg (fun z : ℤ => z^2) hroot
    linarith only [h, hs]
  · push_cast
    rw [add_sub_cancel_right, abs_of_nonneg (by positivity)]
    exact_mod_cast hd
