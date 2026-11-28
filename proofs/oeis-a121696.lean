import OMAStatements.S_oeis_a121696
import Mathlib

-- Problem: A121696, the conjectured recurrence a(n) = (n-1)^2 a(n-2) + n (n-2) a(n-3).
-- Upstream: formal-conjectures statements/oeis-a121696.lean (declaration OMA.S_oeis_a121696.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for all n >= 4).
-- Proof: first a(m+2) + a(m+1) = (m+1)! floor((m+3)/2) for all m, by two-step induction from the
-- defining recursion (a parity case split checks the step). Since a(n) = a(n-2) + n (n-2)! floor((n-1)/2),
-- the recurrence then reduces to an identity of polynomials.

namespace OMA.P_oeis_a121696

open OMA.S_oeis_a121696

theorem T : ∀ m : ℕ, a (m + 2) + a (m + 1) = ((m + 1).factorial : ℤ) * (((m + 3) / 2 : ℕ) : ℤ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => decide
    | 1 => decide
    | m + 2 =>
      have h := ih m (by omega)
      have e4 : a (m + 2 + 2) = a (m + 2) + ((m + 1 : ℕ) + 3 : ℤ) * ((m + 2).factorial : ℤ)
          * (((m + 3) / 2 : ℕ) : ℤ) := by
        rw [show m + 2 + 2 = (m + 1) + 3 from rfl, a]
      have e3 : a (m + 2 + 1) = a (m + 1) + ((m : ℕ) + 3 : ℤ) * ((m + 1).factorial : ℤ)
          * (((m + 2) / 2 : ℕ) : ℤ) := by
        rw [show m + 2 + 1 = m + 3 from rfl, a]
      rw [e4, e3]
      rw [show m + 2 + 1 = m + 3 from rfl, show m + 2 + 3 = m + 5 from rfl]
      rw [Nat.factorial_succ (m + 2), Nat.factorial_succ (m + 1)]
      rcases Nat.even_or_odd' m with ⟨t, rfl | rfl⟩
      · rw [show (2 * t + 3) / 2 = t + 1 by omega, show (2 * t + 2) / 2 = t + 1 by omega,
          show (2 * t + 5) / 2 = t + 2 by omega] at *
        push_cast at h ⊢
        linear_combination h
      · rw [show (2 * t + 1 + 3) / 2 = t + 2 by omega, show (2 * t + 1 + 2) / 2 = t + 1 by omega,
          show (2 * t + 1 + 5) / 2 = t + 3 by omega] at *
        push_cast at h ⊢
        linear_combination h

theorem main' : ∀ n : ℕ, 4 ≤ n →
    a n - ((n : ℤ) - 1) ^ 2 * a (n - 2) - (n : ℤ) * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega]
  have h := T k
  have e : a (k + 4) = a (k + 2) + ((k + 1 : ℕ) + 3 : ℤ) * ((k + 2).factorial : ℤ)
      * (((k + 3) / 2 : ℕ) : ℤ) := by
    rw [show k + 4 = (k + 1) + 3 from rfl, a]
  rw [e, Nat.factorial_succ (k + 1)]
  generalize ((k + 3) / 2 : ℕ) = D at h ⊢
  push_cast
  linear_combination (-((k : ℤ) + 4) * ((k : ℤ) + 2)) * h

end OMA.P_oeis_a121696

theorem OMA.solution : type_of% @OMA.S_oeis_a121696.main := OMA.P_oeis_a121696.main'
