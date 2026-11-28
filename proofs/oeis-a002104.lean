import OMAStatements.S_oeis_a002104
import Mathlib

open OMA.S_oeis_a002104

namespace OMA.P_oeis_a002104

def b (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, n.choose (k + 1) * k.factorial

def c (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.descFactorial k

theorem a_eq (n : ℕ) : a n = (b n : ℤ) := by
  unfold a b
  push_cast
  rw [Finset.range_eq_Ico]
  have := Finset.sum_Ico_add' (fun k => ((n.choose k : ℕ) : ℤ) * ((k - 1).factorial : ℕ)) 0 n 1
  simp only [Nat.add_sub_cancel, zero_add] at this
  rw [this]
  rfl

theorem b_succ (n : ℕ) : b (n + 1) = b n + c n := by
  unfold b c
  simp only [Nat.choose_succ_succ, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ (fun k => n.choose (k + 1) * k.factorial), Nat.choose_succ_self]
  simp only [zero_mul, add_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]

theorem c_succ (n : ℕ) : c (n + 1) = (n + 1) * c n + 1 := by
  unfold c
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.succ_descFactorial_succ, Nat.descFactorial_zero]

end OMA.P_oeis_a002104

open OMA.P_oeis_a002104 in
theorem OMA.solution : type_of% @OMA.S_oeis_a002104.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [e1, e2, e3, a_eq, a_eq, a_eq, a_eq, b_succ (m + 2), b_succ (m + 1), b_succ m,
    c_succ (m + 1), c_succ m]
  push_cast
  ring
