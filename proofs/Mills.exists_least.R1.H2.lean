import OMAReductions.R_Mills_exists_least_R1

-- Step Mills.exists_least.R1.H2: hypothesis H2 of reduction Mills.exists_least.R1

/-!
Mathlib proves `ψ x - θ x ≤ C √x` for some real `C` (`Chebyshev.psi_sub_theta_le_mul_sqrt`).
Replacing `C` by `max C 1` makes the constant positive.
-/

theorem OMA.solution : OMA.R_Mills_exists_least_R1.H2 := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C 1, one_pos.trans_le (le_max_right _ _), fun x => (hC x).trans ?_⟩
  gcongr
  exact le_max_left _ _
