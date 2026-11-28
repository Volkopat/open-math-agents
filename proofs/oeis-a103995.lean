import OMAStatements.S_oeis_a103995

-- Problem: A103995: First column of triangle A103910.
-- Upstream: formal-conjectures statements/oeis-a103995.lean:0 (declaration OMA.S_oeis_a103995.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: row n-1 >= 1 of F*T = I in column 0 reads
-- Sum_{k=0..n-2} F(n-1,k)*T(k,0) + F(n-1,n-1)*T(n-1,0) = 0, and F(n-1,n-1) = 1
-- because P(n-1) is a product of positive Fibonacci numbers. Shifting the index of the sum
-- (i = k+1) gives the recurrence.

namespace R10A103995

open OMA.S_oeis_a103995

theorem fibFact_zero : fibFact 0 = 1 := by
  rw [fibFact, Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num), Finset.prod_empty]

theorem fibFact_ne (n : ℕ) : fibFact n ≠ 0 := by
  unfold fibFact
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  rw [Finset.mem_Icc] at hj
  have hj0 : 0 < j := by omega
  exact Nat.cast_ne_zero.mpr (Nat.fib_pos.mpr hj0).ne'

theorem fib_diag (n : ℕ) : fibonomial n n = 1 := by
  rw [fibonomial, if_pos (le_refl n), Nat.sub_self, fibFact_zero, mul_one]
  exact div_self (fibFact_ne n)

theorem bridge (g : ℕ → ℚ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, g (i - 1) = ∑ k ∈ Finset.range m, g k := by
  induction m with
  | zero =>
    rw [Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num), Finset.sum_empty,
      Finset.range_zero, Finset.sum_empty]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih, Finset.sum_range_succ,
      Nat.add_sub_cancel]

theorem key (T : ℕ → ℕ → ℚ)
    (hright : ∀ n m : ℕ, ∑ k ∈ Finset.range (n + 1), fibonomial n k * T k m =
      if n = m then 1 else 0) (m : ℕ) :
    T (m + 1) 0 = -∑ i ∈ Finset.Icc 1 (m + 1), T (i - 1) 0 * fibonomial (m + 1) (i - 1) := by
  have h := hright (m + 1) 0
  rw [Finset.sum_range_succ, if_neg (show ¬ (m + 1 = 0) by omega), fib_diag, one_mul] at h
  have hb : ∑ i ∈ Finset.Icc 1 (m + 1), T (i - 1) 0 * fibonomial (m + 1) (i - 1) =
      ∑ k ∈ Finset.range (m + 1), T k 0 * fibonomial (m + 1) k :=
    bridge (fun k => T k 0 * fibonomial (m + 1) k) (m + 1)
  have hc : ∑ k ∈ Finset.range (m + 1), T k 0 * fibonomial (m + 1) k =
      ∑ k ∈ Finset.range (m + 1), fibonomial (m + 1) k * T k 0 :=
    Finset.sum_congr rfl (fun k _ => mul_comm (T k 0) (fibonomial (m + 1) k))
  rw [hb, hc]
  linarith

end R10A103995

open OMA.S_oeis_a103995 R10A103995 in
theorem OMA.solution : type_of% @OMA.S_oeis_a103995.main := by
  intro T _hlow hright _hleft n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold a
  rw [show m + 2 - 1 = m + 1 by omega]
  exact key T hright m
