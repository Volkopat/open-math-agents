import OMAStatements.S_oeis_a066534
import Mathlib

/-!
# Mathar's recurrence for OEIS A066534

Credit: @sntntHb (the owner of the agent is credited as the solver)

Proof sketch. Splitting off the last term of `a(n+1) = Sum_{k<n+1} ((n+1)!/k!) 2^k` and using
`(n+1)!/k! = (n+1) * (n!/k!)` for `k ≤ n` gives the first-order relation
`a(n+1) = (n+1) a(n) + (n+1) 2^n`. Writing `n = m + 3` and `P = 2^m`, the three instances
`h3, h2, h1` of this relation (at `m+2`, `m+1`, `m`) satisfy
`LHS of Mathar's recurrence = h3 - 4 h2 + 4 h1`, which `linear_combination` checks.
-/

namespace OMA.A066534Proof

open OMA.S_oeis_a066534

theorem a_succ (n : ℕ) : a (n + 1) = (n + 1) * a n + (n + 1) * 2 ^ n := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial hk.le), mul_assoc]
  · rw [Nat.factorial_succ, Nat.mul_div_assoc _ (dvd_refl _), Nat.div_self (Nat.factorial_pos n)]
    ring

end OMA.A066534Proof

open OMA.S_oeis_a066534 in
theorem OMA.solution : type_of% @OMA.S_oeis_a066534.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h3 := OMA.A066534Proof.a_succ (m + 2)
  have h2 := OMA.A066534Proof.a_succ (m + 1)
  have h1 := OMA.A066534Proof.a_succ m
  simp only [show m + 3 - 1 = m + 2 from rfl, show m + 3 - 2 = m + 1 from rfl,
    show m + 3 - 3 = m from rfl]
  have h3' : (a (m + 3) : ℤ) = ((m : ℤ) + 3) * a (m + 2) + ((m : ℤ) + 3) * (4 * 2 ^ m) := by
    rw [show m + 3 = m + 2 + 1 from rfl, h3]; push_cast; ring
  have h2' : (a (m + 2) : ℤ) = ((m : ℤ) + 2) * a (m + 1) + ((m : ℤ) + 2) * (2 * 2 ^ m) := by
    rw [show m + 2 = m + 1 + 1 from rfl, h2]; push_cast; ring
  have h1' : (a (m + 1) : ℤ) = ((m : ℤ) + 1) * a m + ((m : ℤ) + 1) * 2 ^ m := by
    rw [h1]; push_cast; ring
  push_cast
  linear_combination h3' - 4 * h2' + 4 * h1'
