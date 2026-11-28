import Mathlib.Data.Nat.Factorial.DoubleFactorial

namespace OMA.S_mo_449243

/-- Product of the first positive odd integers. -/
def oddProduct (n : ℕ) : ℤ := Nat.doubleFactorial (2 * n - 1)

/-- The sequence A004208, with the zero term set to zero for the recurrence. -/
def sequence : ℕ → ℤ
  | 0 => 0
  | n + 1 => ((n + 1 : ℕ) : ℤ) * oddProduct (n + 1) -
      (Finset.range n).attach.sum (fun i => sequence (i.val + 1) * oddProduct (n - i.val))
termination_by n => n
decreasing_by exact Nat.succ_lt_succ (Finset.mem_range.mp i.property)

/-- The two recurrences give the same values at the specified indices.
Source: https://mathoverflow.net/questions/449243 -/
def recurrence : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, q => 2 * (q + 2) * recurrence n (q + 1) +
      (Finset.range (q + 1)).sum (fun j => recurrence n j)

theorem main : ∀ n : ℕ, 0 < n → sequence n = (recurrence (n - 1) 0 : ℤ) := by
  sorry

end OMA.S_mo_449243
