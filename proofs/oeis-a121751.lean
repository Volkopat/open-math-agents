import OMAStatements.S_oeis_a121751

-- Problem: A121751: Number of deco polyominoes of height n in which all columns end at an even level. A deco polyomino is a directed column-convex polyomino in which the height, measured along the diagonal, is attained only in the last column.
-- Upstream: formal-conjectures statements/oeis-a121751.lean:0 (declaration OMA.S_oeis_a121751.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! For n ≥ 7 the defining recurrence applies to a(n), ..., a(n-4). For n of a fixed parity the
floors are linear in n, and substituting the five instances makes the left side vanish
identically; the two parities are treated separately. -/

namespace A121751Aux

open OMA.S_oeis_a121751

theorem a_step (k : ℕ) : a (k + 3) = 2 * (((k + 2) / 2 : ℕ) : ℤ) * a (k + 2) -
    ((((k + 2) / 2 : ℕ) : ℤ) * (((k + 1) / 2 : ℕ) : ℤ) - 1) * a (k + 1) := by
  rw [a]

end A121751Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a121751.main := by
  intro n hn
  obtain ⟨j, hj⟩ : ∃ j, n = 2 * j + 7 ∨ n = 2 * j + 8 := ⟨(n - 7) / 2, by omega⟩
  rcases hj with rfl | rfl
  · have e1 : 2 * j + 7 - 1 = 2 * j + 6 := rfl
    have e2 : 2 * j + 7 - 2 = 2 * j + 5 := rfl
    have e3 : 2 * j + 7 - 3 = 2 * j + 4 := rfl
    have e4 : 2 * j + 7 - 4 = 2 * j + 3 := rfl
    have e5 : 2 * j + 7 - 5 = 2 * j + 2 := rfl
    have e6 : 2 * j + 7 - 6 = 2 * j + 1 := rfl
    rw [e1, e2, e3, e4, e5, e6]
    have h0 := A121751Aux.a_step (2 * j + 4)
    have da0 : (2 * j + 4 + 2) / 2 = j + 3 := by omega
    have db0 : (2 * j + 4 + 1) / 2 = j + 2 := by omega
    rw [da0, db0] at h0
    have h1 := A121751Aux.a_step (2 * j + 3)
    have da1 : (2 * j + 3 + 2) / 2 = j + 2 := by omega
    have db1 : (2 * j + 3 + 1) / 2 = j + 2 := by omega
    rw [da1, db1] at h1
    have h2 := A121751Aux.a_step (2 * j + 2)
    have da2 : (2 * j + 2 + 2) / 2 = j + 2 := by omega
    have db2 : (2 * j + 2 + 1) / 2 = j + 1 := by omega
    rw [da2, db2] at h2
    have h3 := A121751Aux.a_step (2 * j + 1)
    have da3 : (2 * j + 1 + 2) / 2 = j + 1 := by omega
    have db3 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [da3, db3] at h3
    have h4 := A121751Aux.a_step (2 * j)
    have da4 : (2 * j + 2) / 2 = j + 1 := by omega
    have db4 : (2 * j + 1) / 2 = j + 0 := by omega
    rw [da4, db4] at h4
    push_cast at h0 h1 h2 h3 h4 ⊢
    linear_combination (256) * h0 +
      (-384 + 512 * ((j : ℤ) + 3)) * h1 +
      (464 - 768 * ((j : ℤ) + 3) + 256 * ((j : ℤ) + 3) ^ 2) * h2 +
      (-272 + 480 * ((j : ℤ) + 3) - 128 * ((j : ℤ) + 3) ^ 2) * h3 +
      (84 - 80 * ((j : ℤ) + 3) + 16 * ((j : ℤ) + 3) ^ 2) * h4
  · have e1 : 2 * j + 8 - 1 = 2 * j + 7 := rfl
    have e2 : 2 * j + 8 - 2 = 2 * j + 6 := rfl
    have e3 : 2 * j + 8 - 3 = 2 * j + 5 := rfl
    have e4 : 2 * j + 8 - 4 = 2 * j + 4 := rfl
    have e5 : 2 * j + 8 - 5 = 2 * j + 3 := rfl
    have e6 : 2 * j + 8 - 6 = 2 * j + 2 := rfl
    rw [e1, e2, e3, e4, e5, e6]
    have h0 := A121751Aux.a_step (2 * j + 5)
    have da0 : (2 * j + 5 + 2) / 2 = j + 3 := by omega
    have db0 : (2 * j + 5 + 1) / 2 = j + 3 := by omega
    rw [da0, db0] at h0
    have h1 := A121751Aux.a_step (2 * j + 4)
    have da1 : (2 * j + 4 + 2) / 2 = j + 3 := by omega
    have db1 : (2 * j + 4 + 1) / 2 = j + 2 := by omega
    rw [da1, db1] at h1
    have h2 := A121751Aux.a_step (2 * j + 3)
    have da2 : (2 * j + 3 + 2) / 2 = j + 2 := by omega
    have db2 : (2 * j + 3 + 1) / 2 = j + 2 := by omega
    rw [da2, db2] at h2
    have h3 := A121751Aux.a_step (2 * j + 2)
    have da3 : (2 * j + 2 + 2) / 2 = j + 2 := by omega
    have db3 : (2 * j + 2 + 1) / 2 = j + 1 := by omega
    rw [da3, db3] at h3
    have h4 := A121751Aux.a_step (2 * j + 1)
    have da4 : (2 * j + 1 + 2) / 2 = j + 1 := by omega
    have db4 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [da4, db4] at h4
    push_cast at h0 h1 h2 h3 h4 ⊢
    linear_combination (256) * h0 +
      (-896 + 512 * ((j : ℤ) + 4)) * h1 +
      (720 - 1024 * ((j : ℤ) + 4) + 256 * ((j : ℤ) + 4) ^ 2) * h2 +
      (-592 + 608 * ((j : ℤ) + 4) - 128 * ((j : ℤ) + 4) ^ 2) * h3 +
      (124 - 96 * ((j : ℤ) + 4) + 16 * ((j : ℤ) + 4) ^ 2) * h4
