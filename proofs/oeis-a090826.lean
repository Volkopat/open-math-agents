import OMAStatements.S_oeis_a090826
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: a(n+2)=a(n+1)+a(n)+catalan(n+1) by splitting the convolution; combine with (n+2)catalan(n+1)=2(2n+1)catalan(n) and ring.

namespace OMA.S_oeis_a090826

lemma cat_rec (n : ℕ) : (n+2) * catalan (n+1) = 2*(2*n+1) * catalan n := by
  have h1 := succ_mul_catalan_eq_centralBinom (n+1)
  have h2 := succ_mul_catalan_eq_centralBinom n
  have h3 := Nat.succ_mul_centralBinom_succ n
  have h4 : (n+1) * ((n+2) * catalan (n+1)) = (n+1) * (2*(2*n+1) * catalan n) := by
    rw [h1, h3, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) h4

lemma a_rec (n : ℕ) : a (n+2) = a (n+1) + a n + catalan (n+1) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (fun j => catalan j * Nat.fib (n+1-j))]
  have : ∀ j ∈ Finset.range (n+1), catalan j * Nat.fib (n+2-j)
      = catalan j * Nat.fib (n-j) + catalan j * Nat.fib (n+1-j) := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show n+2-j = (n-j)+2 by omega, show n+1-j = (n-j)+1 by omega, Nat.fib_add_two]
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  simp
  ring

theorem main_proof : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ)*a n + (-5*(n : ℤ)+6)*a (n-1) + 3*((n : ℤ)-2)*a (n-2)
      + 2*(2*(n : ℤ)-3)*a (n-3) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n-3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [e1, e2, e3]
  have r1 := a_rec m
  have r2 := a_rec (m+1)
  have c := cat_rec (m+1)
  have r1' : (a (m+2) : ℤ) = a (m+1) + a m + catalan (m+1) := by exact_mod_cast r1
  have r2' : (a (m+3) : ℤ) = a (m+2) + a (m+1) + catalan (m+2) := by exact_mod_cast r2
  have c' : ((m:ℤ)+3) * catalan (m+2) = 2*(2*((m:ℤ)+1)+1) * catalan (m+1) := by exact_mod_cast c
  have z1 := sub_eq_zero.mpr r1'
  have z2 := sub_eq_zero.mpr r2'
  have z3 := sub_eq_zero.mpr c'
  push_cast
  have h : ((m:ℤ)+3) * a (m+3) + (-5*((m:ℤ)+3)+6) * a (m+2) + 3*((m:ℤ)+3-2) * a (m+1)
      + 2*(2*((m:ℤ)+3)-3) * a m
      = ((m:ℤ)+3) * ((a (m+3) : ℤ) - (a (m+2) + a (m+1) + catalan (m+2)))
        - (4*(m:ℤ)+6) * ((a (m+2) : ℤ) - (a (m+1) + a m + catalan (m+1)))
        + (((m:ℤ)+3) * catalan (m+2) - 2*(2*((m:ℤ)+1)+1) * catalan (m+1)) := by ring
  rw [h, z1, z2, z3]
  ring


end OMA.S_oeis_a090826

theorem OMA.solution : type_of% @OMA.S_oeis_a090826.main := OMA.S_oeis_a090826.main_proof
