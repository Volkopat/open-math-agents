import OMAStatements.S_oeis_a004395
import Mathlib

-- Problem: A004395: Ratios of successive terms are 1,1,2,3,3,4,5,5,6,7,7,...
-- Upstream: formal-conjectures statements/oeis-a004395.lean:0 (declaration OMA.S_oeis_a004395.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The ratios are r(3k) = 2k+1, r(3k+1) = 2k+1, r(3k+2) = 2k+2. Writing n - 4 as 3k, 3k+1 or
3k+2 expresses a(n-3), ..., a(n) as explicit multiples of a(n-4), and in each of the three cases
the recurrence becomes a polynomial identity in k. -/

namespace A004395Aux

open OMA.S_oeis_a004395

theorem a_succ (n : ℕ) : a (n + 1) = a n * (((2 * n + 3) / 3 : ℕ) : ℤ) := by
  rw [a]

theorem r0 (k : ℕ) : a (3 * k + 1) = a (3 * k) * (2 * (k : ℤ) + 1) := by
  rw [a_succ]
  have h : (2 * (3 * k) + 3) / 3 = 2 * k + 1 := by omega
  rw [h]
  push_cast
  ring

theorem r1 (k : ℕ) : a (3 * k + 2) = a (3 * k + 1) * (2 * (k : ℤ) + 1) := by
  rw [a_succ]
  have h : (2 * (3 * k + 1) + 3) / 3 = 2 * k + 1 := by omega
  rw [h]
  push_cast
  ring

theorem r2 (k : ℕ) : a (3 * k + 3) = a (3 * k + 2) * (2 * (k : ℤ) + 2) := by
  rw [a_succ]
  have h : (2 * (3 * k + 2) + 3) / 3 = 2 * k + 2 := by omega
  rw [h]
  push_cast
  ring

theorem case0 (k : ℕ) :
    243 * a (3 * k + 4) - 216 * a (3 * k + 3) + 54 * (-2 * (3 * (k : ℤ) + 4) + 3) * a (3 * k + 2) +
      6 * (-12 * (3 * (k : ℤ) + 4) ^ 3 + 60 * (3 * (k : ℤ) + 4) ^ 2 - 87 * (3 * (k : ℤ) + 4) + 28) *
        a (3 * k + 1) +
      4 * (2 * (3 * (k : ℤ) + 4) - 5) * (2 * (3 * (k : ℤ) + 4) - 7) * ((3 * (k : ℤ) + 4) - 3) *
        a (3 * k) = 0 := by
  have h1 := r0 k
  have h2 := r1 k
  have h3 := r2 k
  have h4 := r0 (k + 1)
  have e : 3 * (k + 1) + 1 = 3 * k + 4 := by ring
  have e' : 3 * (k + 1) = 3 * k + 3 := by ring
  rw [e, e'] at h4
  push_cast at h4
  rw [h4, h3, h2, h1]
  ring

theorem case1 (k : ℕ) :
    243 * a (3 * k + 5) - 216 * a (3 * k + 4) + 54 * (-2 * (3 * (k : ℤ) + 5) + 3) * a (3 * k + 3) +
      6 * (-12 * (3 * (k : ℤ) + 5) ^ 3 + 60 * (3 * (k : ℤ) + 5) ^ 2 - 87 * (3 * (k : ℤ) + 5) + 28) *
        a (3 * k + 2) +
      4 * (2 * (3 * (k : ℤ) + 5) - 5) * (2 * (3 * (k : ℤ) + 5) - 7) * ((3 * (k : ℤ) + 5) - 3) *
        a (3 * k + 1) = 0 := by
  have h2 := r1 k
  have h3 := r2 k
  have h4 := r0 (k + 1)
  have h5 := r1 (k + 1)
  have e : 3 * (k + 1) + 1 = 3 * k + 4 := by ring
  have e' : 3 * (k + 1) = 3 * k + 3 := by ring
  have e'' : 3 * (k + 1) + 2 = 3 * k + 5 := by ring
  rw [e, e'] at h4
  rw [e'', e] at h5
  push_cast at h4 h5
  rw [h5, h4, h3, h2]
  ring

theorem case2 (k : ℕ) :
    243 * a (3 * k + 6) - 216 * a (3 * k + 5) + 54 * (-2 * (3 * (k : ℤ) + 6) + 3) * a (3 * k + 4) +
      6 * (-12 * (3 * (k : ℤ) + 6) ^ 3 + 60 * (3 * (k : ℤ) + 6) ^ 2 - 87 * (3 * (k : ℤ) + 6) + 28) *
        a (3 * k + 3) +
      4 * (2 * (3 * (k : ℤ) + 6) - 5) * (2 * (3 * (k : ℤ) + 6) - 7) * ((3 * (k : ℤ) + 6) - 3) *
        a (3 * k + 2) = 0 := by
  have h3 := r2 k
  have h4 := r0 (k + 1)
  have h5 := r1 (k + 1)
  have h6 := r2 (k + 1)
  have e : 3 * (k + 1) + 1 = 3 * k + 4 := by ring
  have e' : 3 * (k + 1) = 3 * k + 3 := by ring
  have e'' : 3 * (k + 1) + 2 = 3 * k + 5 := by ring
  have e3 : 3 * (k + 1) + 3 = 3 * k + 6 := by ring
  rw [e, e'] at h4
  rw [e'', e] at h5
  rw [e3, e''] at h6
  push_cast at h4 h5 h6
  rw [h6, h5, h4, h3]
  ring

end A004395Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a004395.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : m + 4 - 1 = m + 3 := by omega
  have e2 : m + 4 - 2 = m + 2 := by omega
  have e3 : m + 4 - 3 = m + 1 := by omega
  rw [e1, e2, e3, Nat.add_sub_cancel]
  obtain ⟨k, hk | hk | hk⟩ : ∃ k, m = 3 * k ∨ m = 3 * k + 1 ∨ m = 3 * k + 2 :=
    ⟨m / 3, by omega⟩
  · subst hk
    have h := A004395Aux.case0 k
    push_cast
    linear_combination h
  · subst hk
    have h := A004395Aux.case1 k
    have f4 : 3 * k + 1 + 4 = 3 * k + 5 := by ring
    have f3 : 3 * k + 1 + 3 = 3 * k + 4 := by ring
    have f2 : 3 * k + 1 + 2 = 3 * k + 3 := by ring
    have f1 : 3 * k + 1 + 1 = 3 * k + 2 := by ring
    rw [f4, f3, f2, f1]
    push_cast
    linear_combination h
  · subst hk
    have h := A004395Aux.case2 k
    have f4 : 3 * k + 2 + 4 = 3 * k + 6 := by ring
    have f3 : 3 * k + 2 + 3 = 3 * k + 5 := by ring
    have f2 : 3 * k + 2 + 2 = 3 * k + 4 := by ring
    have f1 : 3 * k + 2 + 1 = 3 * k + 3 := by ring
    rw [f4, f3, f2, f1]
    push_cast
    linear_combination h
