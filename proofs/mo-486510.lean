import OMAStatements.S_mo_486510

-- Counterexample to the published sign equality: s=5, uc=1, nL=1, nR=2.
-- Source: https://mathoverflow.net/questions/486510
-- Credit: @jaredwilder
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_486510.main) := by
  intro h
  have h0 := h 5 1 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp [OMA.S_mo_486510.weightedSum, Finset.sum_range_succ, OMA.S_mo_486510.eta, Int.sign] at h0
  change (0 : ℤ) = -1 at h0
  exact (by decide : ¬ ((0 : ℤ) = -1)) h0
