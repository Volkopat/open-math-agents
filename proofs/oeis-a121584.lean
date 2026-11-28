import OMAStatements.S_oeis_a121584

-- Problem: A121584: Number of cells in columns 1 and 2 of all deco polyominoes of height n. A deco polyomino is a directed column-convex polyomino in which the height, measured along the diagonal, is attained only in the last column.
-- Upstream: formal-conjectures statements/oeis-a121584.lean:0 (declaration OMA.S_oeis_a121584.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! For n ≥ 6 the defining recurrence applies to a(n), ..., a(n-3). Substituting these 4
instances expresses the left side, multiplied by a nonzero polynomial in n, through a(n-4), ..., a(n-5) and
factorials, and it vanishes identically. -/

namespace A121584Aux

open OMA.S_oeis_a121584

theorem a_step (k : ℕ) : ((k : ℚ) + 3 - 2) * a (k + 3) =
    (2 * ((k : ℚ) + 3) - 3) * a (k + 2) - ((k : ℚ) + 3 - 1) * a (k + 1) +
      (1 / 2) * (2 * ((k : ℚ) + 3) ^ 3 - 9 * ((k : ℚ) + 3) ^ 2 + 17 * ((k : ℚ) + 3) - 16) * ((k + 2).factorial : ℚ) := by
  have hk : (k : ℚ) + 3 - 2 ≠ 0 := by
    have h0 : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
    intro h
    linarith
  rw [a]
  field_simp

end A121584Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a121584.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e1 : m + 6 - 1 = m + 5 := rfl
  have e2 : m + 6 - 2 = m + 4 := rfl
  have e3 : m + 6 - 3 = m + 3 := rfl
  have e4 : m + 6 - 4 = m + 2 := rfl
  have e5 : m + 6 - 5 = m + 1 := rfl
  rw [e1, e2, e3, e4, e5]
  have h0 := A121584Aux.a_step (m + 3)
  have h1 := A121584Aux.a_step (m + 2)
  have h2 := A121584Aux.a_step (m + 1)
  have h3 := A121584Aux.a_step (m)
  simp only [Nat.factorial_succ] at h0 h1 h2 h3
  push_cast at h0 h1 h2 h3 ⊢
  have key : (120 - 154 * ((m : ℚ) + 6) + 71 * ((m : ℚ) + 6) ^ 2 - 14 * ((m : ℚ) + 6) ^ 3 + ((m : ℚ) + 6) ^ 4) * ((14 - 14 * ((m : ℚ) + 6)) * OMA.S_oeis_a121584.a (m + 6) + (-6995 + 1731 * ((m : ℚ) + 6) + 14 * ((m : ℚ) + 6) ^ 2) * OMA.S_oeis_a121584.a (m + 5) + (21729 + 1440 * ((m : ℚ) + 6) - 1731 * ((m : ℚ) + 6) ^ 2) * OMA.S_oeis_a121584.a (m + 4) + (12008 - 23904 * ((m : ℚ) + 6) + 5562 * ((m : ℚ) + 6) ^ 2) * OMA.S_oeis_a121584.a (m + 3) + (-54220 + 36181 * ((m : ℚ) + 6) - 5987 * ((m : ℚ) + 6) ^ 2) * OMA.S_oeis_a121584.a (m + 2) + (27464 - 15434 * ((m : ℚ) + 6) + 2142 * ((m : ℚ) + 6) ^ 2) * OMA.S_oeis_a121584.a (m + 1)) = 0 := by
    linear_combination (-840 + 1498 * ((m : ℚ) + 6) - 826 * ((m : ℚ) + 6) ^ 2 + 182 * ((m : ℚ) + 6) ^ 3 - 14 * ((m : ℚ) + 6) ^ 4) * h0 +
    (278960 - 333272 * ((m : ℚ) + 6) + 140931 * ((m : ℚ) + 6) ^ 2 - 25182 * ((m : ℚ) + 6) ^ 3 + 1549 * ((m : ℚ) + 6) ^ 4 + 14 * ((m : ℚ) + 6) ^ 5) * h1 +
    (-302960 + 160972 * ((m : ℚ) + 6) + 105304 * ((m : ℚ) + 6) ^ 2 - 92021 * ((m : ℚ) + 6) ^ 3 + 21904 * ((m : ℚ) + 6) ^ 4 - 1703 * ((m : ℚ) + 6) ^ 5) * h2 +
    (-823920 + 1314404 * ((m : ℚ) + 6) - 817354 * ((m : ℚ) + 6) ^ 2 + 248206 * ((m : ℚ) + 6) ^ 3 - 36854 * ((m : ℚ) + 6) ^ 4 + 2142 * ((m : ℚ) + 6) ^ 5) * h3
  have hD : (120 - 154 * ((m : ℚ) + 6) + 71 * ((m : ℚ) + 6) ^ 2 - 14 * ((m : ℚ) + 6) ^ 3 + ((m : ℚ) + 6) ^ 4) ≠ 0 := by
    have e : (120 - 154 * ((m : ℚ) + 6) + 71 * ((m : ℚ) + 6) ^ 2 - 14 * ((m : ℚ) + 6) ^ 3 + ((m : ℚ) + 6) ^ 4) = ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) := by ring
    rw [e]
    have h0 : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
    positivity
  have h := (mul_eq_zero.mp key).resolve_left hD
  linear_combination h
