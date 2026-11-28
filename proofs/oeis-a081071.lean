import OMAStatements.S_oeis_a081071
import Mathlib

open Nat Finset
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: Lucas(m+1) = F(m) + F(m+2) by strong induction, and the even-index
-- Fibonacci sum satisfies F(0) + F(2) + ... + F(2m) + 1 = F(2m+1). Hence the sum over
-- k in [2, 2n] equals F(4n+1) - 2, and the right side is F(4n+3) + F(4n+1) - 2 = L(4n+2) - 2.

namespace OMA.A081071Proof

open OMA.S_oeis_a081071

theorem lucas_succ : ∀ m : ℕ, lucas (m + 1) = fib m + fib (m + 2)
  | 0 => by simp [lucas, fib_two]
  | 1 => by
      simp [lucas, fib_add_two]
  | (m + 2) => by
      have h1 := lucas_succ m
      have h2 := lucas_succ (m + 1)
      show lucas (m + 2) + lucas (m + 1) = _
      rw [h2, h1]
      have e1 : fib (m + 1 + 2) = fib (m + 1) + fib (m + 2) := fib_add_two
      have e2 : fib (m + 2 + 2) = fib (m + 2) + fib (m + 1 + 2) := by
        rw [show m + 2 + 2 = (m + 2) + 2 from rfl, fib_add_two]
      have e3 : fib (m + 2) = fib m + fib (m + 1) := fib_add_two
      rw [e2, e1, e3]
      ring

theorem even_sum : ∀ m : ℕ,
    (∑ k ∈ range (m + 1), fib (2 * k)) + 1 = fib (2 * m + 1)
  | 0 => by simp
  | (m + 1) => by
      rw [sum_range_succ, add_right_comm, even_sum m]
      have : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
      rw [this, fib_add_two]
      have h2 : 2 * (m + 1) = 2 * m + 2 := by ring
      rw [h2, show 2 * m + 1 + 1 = 2 * m + 2 from rfl]

theorem icc_sum (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Icc 2 (2 * n), fib (2 * k)) + 2 = fib (4 * n + 1) := by
  have hsplit : range (2 * n + 1) = {0, 1} ∪ Icc 2 (2 * n) := by
    ext x; simp [mem_Icc]; omega
  have hdisj : Disjoint ({0, 1} : Finset ℕ) (Icc 2 (2 * n)) := by
    rw [disjoint_left]; intro x hx; simp at hx; simp [mem_Icc]; omega
  have h := even_sum (2 * n)
  rw [hsplit, sum_union hdisj] at h
  simp [fib_two] at h
  rw [show 4 * n + 1 = 2 * (2 * n) + 1 by ring, ← h]
  ring

end OMA.A081071Proof

open OMA.A081071Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a081071.main := by
  intro n hn
  unfold OMA.S_oeis_a081071.a
  have hL : OMA.S_oeis_a081071.lucas (4 * n + 2) = fib (4 * n + 1) + fib (4 * n + 3) :=
    lucas_succ (4 * n + 1)
  have hs := icc_sum n hn
  have h2 : 2 ≤ fib (4 * n + 1) := by omega
  omega
