import OMAStatements.S_oeis_a203472
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators

-- Proof of the conjecture stated in OEIS A203472. Splitting off the last factor gives
-- a (m + 2) = a (m + 1) * P m, where P m = (m + 7) (m + 8) ... (2 m + 7) is a product of m + 1
-- consecutive integers, hence divisible by (m + 1)!. Since superFactorial (m + 1) is
-- (m + 1)! * superFactorial m, induction on m gives superFactorial m ∣ a (m + 1).

/-- Splitting off the factor `j = m + 4` of `a (m + 2)`. -/
theorem OMA.a203472_step (m : ℕ) :
    OMA.S_oeis_a203472.a (m + 1 + 1) =
      OMA.S_oeis_a203472.a (m + 1) * ∏ i ∈ Finset.Ico 3 (m + 4), (i + (m + 4)) := by
  unfold OMA.S_oeis_a203472.a
  rw [show m + 1 + 1 + 2 = (m + 3) + 1 by omega, Finset.prod_Icc_succ_top (by omega)]

/-- The new factor is a product of `m + 1` consecutive integers. -/
theorem OMA.a203472_dvd (m : ℕ) :
    (m + 1).factorial ∣ ∏ i ∈ Finset.Ico 3 (m + 4), (i + (m + 4)) := by
  have h : ∏ i ∈ Finset.Ico 3 (m + 4), (i + (m + 4)) = (m + 7).ascFactorial (m + 1) := by
    rw [Finset.prod_Ico_eq_prod_range, Nat.ascFactorial_eq_prod_range,
      show m + 4 - 3 = m + 1 by omega]
    exact Finset.prod_congr rfl (fun k _ => by omega)
  rw [h]
  exact Nat.factorial_dvd_ascFactorial _ _

theorem OMA.solution : type_of% @OMA.S_oeis_a203472.main := by
  have key : ∀ m : ℕ, Nat.superFactorial m ∣ OMA.S_oeis_a203472.a (m + 1) := by
    intro m
    induction m with
    | zero => rw [Nat.superFactorial_zero]; exact one_dvd _
    | succ m ih =>
      rw [Nat.superFactorial_succ, OMA.a203472_step, Nat.mul_comm ((m + 1).factorial)]
      exact Nat.mul_dvd_mul ih (OMA.a203472_dvd m)
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using key m
