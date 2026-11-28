import OMAStatements.S_oeis_a002627
import Mathlib

open OMA.S_oeis_a002627 in
theorem OMA.solution : type_of% @OMA.S_oeis_a002627.main := by
  first
  | (have hS : ∀ n, ∑ k ∈ Finset.Icc 1 (n + 1), (Nat.factorial (n + 1) / Nat.factorial k) * a k =
         (n + 1) * ∑ k ∈ Finset.Icc 1 n, (Nat.factorial n / Nat.factorial k) * a k + a (n + 1) := by
       intro n
       rw [Finset.sum_Icc_succ_top (by omega), Nat.div_self (Nat.factorial_pos _), one_mul,
         Finset.mul_sum]
       congr 1
       apply Finset.sum_congr rfl
       intro k hk
       rw [Finset.mem_Icc] at hk
       rw [Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial hk.2), mul_assoc]
     refine ⟨?_, ?_⟩
     · intro n hn
       obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
       rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
       have r1 : a (m + 2) = (m + 2) * a (m + 1) + 1 := rfl
       have r0 : a (m + 1) = (m + 1) * a m + 1 := rfl
       rw [r1, r0]
       push_cast
       ring
     · intro n
       induction n with
       | zero => simp [a]
       | succ n ih =>
         rw [hS n]
         have hr1 : a (n + 1 + 1) = (n + 1 + 1) * a (n + 1) + 1 := rfl
         have hr2 : a (n + 1) = (n + 1) * a n + 1 := rfl
         rw [hr1, Nat.factorial_succ]
         generalize (∑ k ∈ Finset.Icc 1 n, (Nat.factorial n / Nat.factorial k) * a k) = S at ih ⊢
         zify at ih hr2 ⊢
         linear_combination ((n : ℤ) + 1) * ih - hr2)
  | (intro n hn
     obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
     rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
     simp only [OMA.S_oeis_a002627.a]
     push_cast
     ring)
  | (intro n hn
     obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
     rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
     simp only [OMA.S_oeis_a002627.a]
     ring)
