import OMAStatements.S_oeis_a082031
import Mathlib

-- Problem: A082031: Expansion of e.g.f. exp(2*x)/(1-x)^3.
-- Upstream: formal-conjectures statements/oeis-a082031.lean:0 (declaration OMA.S_oeis_a082031.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! With d(n,k) = C(n,k) k!, let u, v, w be the sums of d(n,k) 2^(n-k) with weights 1, k+1 and
C(k+2,2); then a = w. The shift d(n+1,k+1) = (n+1) d(n,k) gives u(n+1) = 2^(n+1) + (n+1) u(n),
v(n+1) = 2^(n+1) + (n+1)(v(n) + u(n)) and w(n+1) = 2^(n+1) + (n+1)(w(n) + v(n) + u(n)). By
induction v(n) = (n-1) u(n) + 2^(n+1) and 2 w(n) = (n^2 - n + 2) u(n) + n 2^(n+1), and the
recurrence follows from the one for u. -/

namespace A082031Aux

open OMA.S_oeis_a082031

def u (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (n.descFactorial k : ℤ) * 2 ^ (n - k)

def v (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((k : ℤ) + 1) * (n.descFactorial k : ℤ) * 2 ^ (n - k)

def w (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((k + 2).choose 2 : ℤ) * (n.descFactorial k : ℤ) * 2 ^ (n - k)

theorem a_eq (n : ℕ) : a n = w n := by
  unfold a w
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

theorem u_succ (n : ℕ) : u (n + 1) = 2 ^ (n + 1) + ((n : ℤ) + 1) * u n := by
  unfold u
  rw [Finset.sum_range_succ' (fun k => ((n + 1).descFactorial k : ℤ) * 2 ^ (n + 1 - k)),
    Finset.mul_sum]
  simp only [Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero, one_mul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.succ_descFactorial_succ, Nat.add_sub_add_right]
  push_cast
  ring

theorem v_succ (n : ℕ) : v (n + 1) = 2 ^ (n + 1) + ((n : ℤ) + 1) * (v n + u n) := by
  unfold u v
  rw [Finset.sum_range_succ' (fun k => ((k : ℤ) + 1) * ((n + 1).descFactorial k : ℤ) *
    2 ^ (n + 1 - k)), ← Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero, Nat.cast_zero, zero_add, one_mul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.succ_descFactorial_succ, Nat.add_sub_add_right]
  push_cast
  ring

theorem w_succ (n : ℕ) : w (n + 1) = 2 ^ (n + 1) + ((n : ℤ) + 1) * (w n + v n + u n) := by
  unfold u v w
  rw [Finset.sum_range_succ' (fun k => ((k + 2).choose 2 : ℤ) * ((n + 1).descFactorial k : ℤ) *
    2 ^ (n + 1 - k)), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero, zero_add, Nat.choose_self,
    one_mul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hc : ((k + 1 + 2).choose 2 : ℤ) = ((k + 2).choose 2 : ℤ) + ((k : ℤ) + 2) := by
    have h : (k + 1 + 2).choose 2 = (k + 2).choose 1 + (k + 2).choose 2 := by
      rw [show k + 1 + 2 = (k + 2) + 1 from by ring, Nat.choose_succ_succ]
    rw [h, Nat.choose_one_right]
    push_cast
    ring
  rw [Nat.succ_descFactorial_succ, Nat.add_sub_add_right, hc]
  push_cast
  ring

theorem v_closed (n : ℕ) : v n = ((n : ℤ) - 1) * u n + 2 ^ (n + 1) := by
  induction n with
  | zero => simp [u, v]
  | succ n ih =>
    rw [v_succ, u_succ, ih]
    push_cast
    ring

theorem w_closed (n : ℕ) : 2 * w n = ((n : ℤ) ^ 2 - n + 2) * u n + n * 2 ^ (n + 1) := by
  induction n with
  | zero => simp [u, w]
  | succ n ih =>
    have e : 2 * w (n + 1) = 2 * 2 ^ (n + 1) + ((n : ℤ) + 1) * (2 * w n + 2 * v n + 2 * u n) := by
      rw [w_succ]
      ring
    rw [e, ih, v_closed, u_succ]
    push_cast
    ring

theorem rec (m : ℕ) :
    w (m + 2) + (-((m : ℤ) + 2) - 4) * w (m + 1) + 2 * (((m : ℤ) + 2) - 1) * w m = 0 := by
  have h2 := w_closed (m + 2)
  have h1 := w_closed (m + 1)
  have h0 := w_closed m
  have hu2 := u_succ (m + 1)
  have hu1 := u_succ m
  push_cast at h2 h1 hu2
  have key : 2 * (w (m + 2) + (-((m : ℤ) + 2) - 4) * w (m + 1) +
      2 * (((m : ℤ) + 2) - 1) * w m) = 0 := by
    have e : 2 * (w (m + 2) + (-((m : ℤ) + 2) - 4) * w (m + 1) +
        2 * (((m : ℤ) + 2) - 1) * w m) =
        2 * w (m + 2) + (-((m : ℤ) + 2) - 4) * (2 * w (m + 1)) +
          2 * (((m : ℤ) + 2) - 1) * (2 * w m) := by ring
    rw [e, h2, h1, h0, hu2, hu1]
    ring
  exact (mul_eq_zero.mp key).resolve_left (by norm_num)

end A082031Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a082031.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  rw [e1, Nat.add_sub_cancel, A082031Aux.a_eq, A082031Aux.a_eq, A082031Aux.a_eq]
  have h := A082031Aux.rec m
  push_cast
  exact h
