import OMAReductions.R_oeis_a191625_R1

-- Step oeis-a191625.R1.H1: hypothesis H1 of reduction oeis-a191625.R1
-- Credit: @JarethWayneHill
-- H1 := let t : PowerSeries ℤ := X   ∃ u : PowerSeries ℤ, constantCoeff u = 0 ∧ t*u^2 + (-t^3-t^2+t-1)*u + t = 0

theorem OMA.solution : OMA.R_oeis_a191625_R1.H1 := by
  exact OMA.R_oeis_a191625_R1.auxiliary_exists
