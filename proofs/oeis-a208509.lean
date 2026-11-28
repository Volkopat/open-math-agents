import OMAStatements.S_oeis_a208509
import Mathlib

open OMA.S_oeis_a208509


theorem P_coeff (m : ℕ) : ∀ k : ℕ,
    (P m).1.coeff k = (if k = 0 then 1 else Nat.choose m (2 * k) + Nat.choose (m + 1) (2 * k)) ∧
    (P m).2.coeff k = Nat.choose m (2 * k + 1) + Nat.choose (m + 1) (2 * k + 1) := by
  induction m with
  | zero =>
    intro k
    simp only [P, Polynomial.coeff_one]
    rcases k with _ | k
    · simp
    · have e1 : Nat.choose 0 (2 * (k + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have e2 : Nat.choose 1 (2 * (k + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have e3 : Nat.choose 0 (2 * (k + 1) + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have e4 : Nat.choose 1 (2 * (k + 1) + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [e1, e2, e3, e4]
  | succ m ih =>
    intro k
    simp only [P, Polynomial.coeff_add, Polynomial.coeff_one]
    rcases k with _ | k
    · refine ⟨?_, ?_⟩
      · simp [(ih 0).1]
      · rw [(ih 0).1, (ih 0).2]
        simp [Nat.choose_one_right]
        omega
    · refine ⟨?_, ?_⟩
      · rw [Polynomial.coeff_X_mul, (ih (k + 1)).1, (ih k).2]
        simp only [show k + 1 ≠ 0 from by omega, if_false]
        have e1 := Nat.choose_succ_succ' m (2 * k + 1)
        have e2 := Nat.choose_succ_succ' (m + 1) (2 * k + 1)
        have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
        rw [h1]
        omega
      · rw [(ih (k + 1)).1, (ih (k + 1)).2]
        simp only [show k + 1 ≠ 0 from by omega, if_false, add_zero]
        have e1 := Nat.choose_succ_succ' m (2 * (k + 1))
        have e2 := Nat.choose_succ_succ' (m + 1) (2 * (k + 1))
        omega

theorem OMA.solution : type_of% @OMA.S_oeis_a208509.main := by
  intro n k hn _
  unfold T
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact (P_coeff m k).2
