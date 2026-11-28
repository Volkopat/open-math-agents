import OMAStatements.S_oeis_a121747

-- Problem: A121747: Number of columns of odd length in all deco polyominoes of height n. A deco polyomino is a directed column-convex polyomino in which the height, measured along the diagonal, is attained only in the last column.
-- Upstream: formal-conjectures statements/oeis-a121747.lean:0 (declaration OMA.S_oeis_a121747.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! For n ≥ 6 the defining recurrence applies to a(n), ..., a(n-4). Substituting these instances
removes the terms a(k) and leaves a combination of d(n-1), ..., d(n-5) and factorials. For n of a
fixed parity the relations d(2k+1) = -d(2k) and d(2k+2) = d(2k) + (2k+1)! reduce it to zero; the two
parities are treated separately. -/

namespace A121747Aux

open OMA.S_oeis_a121747

theorem a_step (k : ℕ) : a (k + 2) =
    ((k : ℤ) + 2) * a (k + 1) - d (k + 1) + ((k + 1).factorial : ℤ) * (((k + 2) / 2 : ℕ) : ℤ) := by
  rw [a]

theorem d_even (k : ℕ) : d (2 * k + 2) = d (2 * k) + ((2 * k + 1).factorial : ℤ) := by
  have e : (2 * k) % 2 = 0 := by omega
  rw [d, if_pos e]

theorem d_odd (k : ℕ) : d (2 * k + 3) = -(d (2 * k + 2)) := by
  have e : ¬ ((2 * k + 1) % 2 = 0) := by omega
  rw [d, if_neg e]

theorem d_one : d 1 = -(d 0) := by
  rw [d, d]
  norm_num

theorem d_odd' (k : ℕ) : d (2 * k + 1) = -(d (2 * k)) := by
  cases k with
  | zero => exact d_one
  | succ k => exact d_odd k

end A121747Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a121747.main := by
  intro n hn
  obtain ⟨j, hj⟩ : ∃ j, n = 2 * j + 6 ∨ n = 2 * j + 7 := ⟨(n - 6) / 2, by omega⟩
  rcases hj with rfl | rfl
  · have e1 : 2 * j + 6 - 1 = 2 * j + 5 := rfl
    have e2 : 2 * j + 6 - 2 = 2 * j + 4 := rfl
    have e3 : 2 * j + 6 - 3 = 2 * j + 3 := rfl
    have e4 : 2 * j + 6 - 4 = 2 * j + 2 := rfl
    have e5 : 2 * j + 6 - 5 = 2 * j + 1 := rfl
    rw [e1, e2, e3, e4, e5]
    have h0 := A121747Aux.a_step (2 * j + 4)
    have f0 : (2 * j + 4 + 2) / 2 = j + 3 := by omega
    rw [f0] at h0
    have h1 := A121747Aux.a_step (2 * j + 3)
    have f1 : (2 * j + 3 + 2) / 2 = j + 2 := by omega
    rw [f1] at h1
    have h2 := A121747Aux.a_step (2 * j + 2)
    have f2 : (2 * j + 2 + 2) / 2 = j + 2 := by omega
    rw [f2] at h2
    have h3 := A121747Aux.a_step (2 * j + 1)
    have f3 : (2 * j + 1 + 2) / 2 = j + 1 := by omega
    rw [f3] at h3
    have h4 := A121747Aux.a_step (2 * j)
    have f4 : (2 * j + 2) / 2 = j + 1 := by omega
    rw [f4] at h4
    have r1 : OMA.S_oeis_a121747.d (2 * j + 5) = -(OMA.S_oeis_a121747.d (2 * j + 4)) := A121747Aux.d_odd' (j + 2)
    have r2 : OMA.S_oeis_a121747.d (2 * j + 4) = OMA.S_oeis_a121747.d (2 * j + 2) + ((2 * j + 3).factorial : ℤ) := A121747Aux.d_even (j + 1)
    have r3 : OMA.S_oeis_a121747.d (2 * j + 3) = -(OMA.S_oeis_a121747.d (2 * j + 2)) := A121747Aux.d_odd' (j + 1)
    have r4 : OMA.S_oeis_a121747.d (2 * j + 2) = OMA.S_oeis_a121747.d (2 * j) + ((2 * j + 1).factorial : ℤ) := A121747Aux.d_even (j)
    have r5 : OMA.S_oeis_a121747.d (2 * j + 1) = -(OMA.S_oeis_a121747.d (2 * j)) := A121747Aux.d_odd' (j)
    simp only [Nat.factorial_succ] at h0 h1 h2 h3 h4 r1 r2 r3 r4 r5
    push_cast at h0 h1 h2 h3 h4 r1 r2 r3 r4 r5 ⊢
    linear_combination (38 - 9 * (2 * (j : ℤ) + 6)) * h0 +
      (81 - 19 * (2 * (j : ℤ) + 6)) * h1 +
      (46 + 76 * (2 * (j : ℤ) + 6) - 56 * (2 * (j : ℤ) + 6) ^ 2 + 9 * (2 * (j : ℤ) + 6) ^ 3) * h2 +
      (-177 + 419 * (2 * (j : ℤ) + 6) - 204 * (2 * (j : ℤ) + 6) ^ 2 + 28 * (2 * (j : ℤ) + 6) ^ 3) * h3 +
      (-180 + 333 * (2 * (j : ℤ) + 6) - 148 * (2 * (j : ℤ) + 6) ^ 2 + 19 * (2 * (j : ℤ) + 6) ^ 3) * h4 +
      (-38 + 9 * (2 * (j : ℤ) + 6)) * r1 +
      (-43 + 10 * (2 * (j : ℤ) + 6)) * r2 +
      (-46 - 76 * (2 * (j : ℤ) + 6) + 56 * (2 * (j : ℤ) + 6) ^ 2 - 9 * (2 * (j : ℤ) + 6) ^ 3) * r3 +
      (180 - 333 * (2 * (j : ℤ) + 6) + 148 * (2 * (j : ℤ) + 6) ^ 2 - 19 * (2 * (j : ℤ) + 6) ^ 3) * r4 +
      (180 - 333 * (2 * (j : ℤ) + 6) + 148 * (2 * (j : ℤ) + 6) ^ 2 - 19 * (2 * (j : ℤ) + 6) ^ 3) * r5
  · have e1 : 2 * j + 7 - 1 = 2 * j + 6 := rfl
    have e2 : 2 * j + 7 - 2 = 2 * j + 5 := rfl
    have e3 : 2 * j + 7 - 3 = 2 * j + 4 := rfl
    have e4 : 2 * j + 7 - 4 = 2 * j + 3 := rfl
    have e5 : 2 * j + 7 - 5 = 2 * j + 2 := rfl
    rw [e1, e2, e3, e4, e5]
    have h0 := A121747Aux.a_step (2 * j + 5)
    have f0 : (2 * j + 5 + 2) / 2 = j + 3 := by omega
    rw [f0] at h0
    have h1 := A121747Aux.a_step (2 * j + 4)
    have f1 : (2 * j + 4 + 2) / 2 = j + 3 := by omega
    rw [f1] at h1
    have h2 := A121747Aux.a_step (2 * j + 3)
    have f2 : (2 * j + 3 + 2) / 2 = j + 2 := by omega
    rw [f2] at h2
    have h3 := A121747Aux.a_step (2 * j + 2)
    have f3 : (2 * j + 2 + 2) / 2 = j + 2 := by omega
    rw [f3] at h3
    have h4 := A121747Aux.a_step (2 * j + 1)
    have f4 : (2 * j + 1 + 2) / 2 = j + 1 := by omega
    rw [f4] at h4
    have r1 : OMA.S_oeis_a121747.d (2 * j + 6) = OMA.S_oeis_a121747.d (2 * j + 4) + ((2 * j + 5).factorial : ℤ) := A121747Aux.d_even (j + 2)
    have r2 : OMA.S_oeis_a121747.d (2 * j + 5) = -(OMA.S_oeis_a121747.d (2 * j + 4)) := A121747Aux.d_odd' (j + 2)
    have r3 : OMA.S_oeis_a121747.d (2 * j + 4) = OMA.S_oeis_a121747.d (2 * j + 2) + ((2 * j + 3).factorial : ℤ) := A121747Aux.d_even (j + 1)
    have r4 : OMA.S_oeis_a121747.d (2 * j + 3) = -(OMA.S_oeis_a121747.d (2 * j + 2)) := A121747Aux.d_odd' (j + 1)
    simp only [Nat.factorial_succ] at h0 h1 h2 h3 h4 r1 r2 r3 r4
    push_cast at h0 h1 h2 h3 h4 r1 r2 r3 r4 ⊢
    linear_combination (38 - 9 * (2 * (j : ℤ) + 7)) * h0 +
      (81 - 19 * (2 * (j : ℤ) + 7)) * h1 +
      (46 + 76 * (2 * (j : ℤ) + 7) - 56 * (2 * (j : ℤ) + 7) ^ 2 + 9 * (2 * (j : ℤ) + 7) ^ 3) * h2 +
      (-177 + 419 * (2 * (j : ℤ) + 7) - 204 * (2 * (j : ℤ) + 7) ^ 2 + 28 * (2 * (j : ℤ) + 7) ^ 3) * h3 +
      (-180 + 333 * (2 * (j : ℤ) + 7) - 148 * (2 * (j : ℤ) + 7) ^ 2 + 19 * (2 * (j : ℤ) + 7) ^ 3) * h4 +
      (-38 + 9 * (2 * (j : ℤ) + 7)) * r1 +
      (-81 + 19 * (2 * (j : ℤ) + 7)) * r2 +
      (-3 - 86 * (2 * (j : ℤ) + 7) + 56 * (2 * (j : ℤ) + 7) ^ 2 - 9 * (2 * (j : ℤ) + 7) ^ 3) * r3 +
      (177 - 419 * (2 * (j : ℤ) + 7) + 204 * (2 * (j : ℤ) + 7) ^ 2 - 28 * (2 * (j : ℤ) + 7) ^ 3) * r4
