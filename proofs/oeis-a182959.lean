import OMAStatements.S_oeis_a182959

-- The proof uses the central binomial coefficient recurrence twice and
-- clears the positive rational denominators in one step.

open OMA.S_oeis_a182959

private lemma centralBinom_ratio (m : ℕ) :
    ((m + 1).centralBinom : ℚ) = 2 * (2 * (m : ℚ) + 1) * m.centralBinom / (m + 1) := by
  apply (eq_div_iff (by positivity)).2
  rw [mul_comm]
  exact_mod_cast Nat.succ_mul_centralBinom_succ m

theorem OMA.solution : type_of% @OMA.S_oeis_a182959.main := by
  refine ⟨4, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 + 2 := ⟨n - 4, by omega⟩
  rw [show m + 2 + 2 - 1 = m + 1 + 2 by omega, show m + 2 + 2 - 2 = m + 2 by omega]
  simp only [a]
  rw [show m + 2 + 1 = m + 1 + 1 + 1 by omega,
    centralBinom_ratio (m + 1 + 1), centralBinom_ratio (m + 1)]
  push_cast
  field_simp (disch := positivity)
  ring
