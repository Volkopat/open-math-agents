import OMAStatements.S_oeis_a268554

-- Problem: A268554: Diagonal of the rational function 1/((1 - w - u v) * (1 - x y - x z - y z)).
-- Upstream: formal-conjectures statements/oeis-a268554.lean:0 (declaration OMA.S_oeis_a268554.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Expanding (4n)!, (3n)!, (2n)! and n! one step from n-1 to n shows that a(n)/a(n-1) is
6 (4n-1) (4n-3) (3n-1) (3n-2) / (n^3 (2n-1)). -/

theorem OMA.solution : type_of% @OMA.S_oeis_a268554.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  unfold OMA.S_oeis_a268554.a
  have e4 : 4 * (m + 1) = 4 * m + 3 + 1 := by ring
  have e3 : 3 * (m + 1) = 3 * m + 2 + 1 := by ring
  have e2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
  rw [e4, e3, e2]
  simp only [Nat.factorial_succ]
  have h1 : (m.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h4 : 2 * (m : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring
