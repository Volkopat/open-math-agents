import OMAStatements.S_oeis_a193665
import Mathlib

-- Problem: A193665, the recurrence a(n) + (-n-4) a(n-1) + (n+1) a(n-2) - a(n-3) = 0 for
-- a(n) = Sum_{k=0..n} (k+1)(n+1) r(n-k).
-- Upstream: formal-conjectures statements/oeis-a193665.lean (declaration OMA.S_oeis_a193665.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated recurrence holds for n >= 3).
-- Proof: a(n) = r(n+1) = (n+1) s(n) with s(k) = Sum_{i<=k} (i+1) r(k-i); the second difference of s
-- is r, which gives s(k+2) = (k+4) s(k+1) - s(k).

namespace OMA.P_oeis_a193665

open OMA.S_oeis_a193665 Finset

def s (k : ℕ) : ℤ := ∑ i ∈ range (k + 1), ((i : ℤ) + 1) * r (k - i)

def t (k : ℕ) : ℤ := ∑ i ∈ range (k + 1), r (k - i)

theorem r_succ (k : ℕ) : r (k + 1) = ((k : ℤ) + 1) * s k := by
  rw [r, Fin.sum_univ_eq_sum_range (fun i => (((i : ℤ) + 1) * ((k : ℤ) + 1)) * r (k - i)) (k + 1),
    s, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

theorem a_eq (n : ℕ) : a n = r (n + 1) := by
  rw [r_succ, a, s, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

theorem t_succ (k : ℕ) : t (k + 1) = t k + r (k + 1) := by
  rw [t, sum_range_succ']
  simp only [Nat.add_sub_add_right, Nat.sub_zero]
  rfl

theorem s_succ (k : ℕ) : s (k + 1) = s k + t (k + 1) := by
  rw [t_succ, s, sum_range_succ', s, t]
  simp only [Nat.add_sub_add_right, Nat.sub_zero]
  push_cast
  rw [show (∑ i ∈ range (k + 1), ((i : ℤ) + 1 + 1) * r (k - i)) =
      ∑ i ∈ range (k + 1), ((i : ℤ) + 1) * r (k - i) + ∑ i ∈ range (k + 1), r (k - i) by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring]
  ring

theorem s_rec (k : ℕ) : s (k + 2) = ((k : ℤ) + 4) * s (k + 1) - s k := by
  have h1 := s_succ (k + 1)
  have h2 := s_succ k
  have h3 := t_succ (k + 1)
  have h4 := r_succ (k + 1)
  push_cast at h4
  linear_combination h1 + h3 + h4 - h2

theorem main' : ∀ n : ℕ, 3 ≤ n →
    a n + (-(n : ℤ) - 4) * a (n - 1) + ((n : ℤ) + 1) * a (n - 2) - a (n - 3) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  simp only [a_eq, r_succ]
  have e3 := s_rec (m + 1)
  have e2 := s_rec m
  push_cast at e3 e2 ⊢
  linear_combination ((m : ℤ) + 4) * e3 - ((m : ℤ) + 1) * e2

end OMA.P_oeis_a193665

theorem OMA.solution : type_of% @OMA.S_oeis_a193665.main := OMA.P_oeis_a193665.main'
