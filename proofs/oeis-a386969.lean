import OMAStatements.S_oeis_a386969
import Mathlib.Tactic

namespace OMA.P_oeis_a386969
open OMA.S_oeis_a386969

private lemma a_one (a : ℕ → ℕ) (ha0 : a 0 = 0)
    (hnext : ∀ n, a (n + 1) = nextValue a n) : a 1 = 4 := by
  rw [hnext 0, nextValue]
  split_ifs <;> omega

private lemma a_two (a : ℕ → ℕ) (ha0 : a 0 = 0)
    (hnext : ∀ n, a (n + 1) = nextValue a n) : a 2 = 2 := by
  have ha1 := a_one a ha0 hnext
  rw [hnext 1, nextValue]
  split_ifs with h
  · omega
  · exfalso
    apply h
    refine ⟨by omega, fun i => ?_⟩
    rcases i with ⟨i, hi⟩
    dsimp
    interval_cases i <;> omega

private lemma a_three (a : ℕ → ℕ) (ha0 : a 0 = 0)
    (hnext : ∀ n, a (n + 1) = nextValue a n) : a 3 = 8 := by
  have ha2 := a_two a ha0 hnext
  rw [hnext 2, nextValue]
  split_ifs <;> omega

private lemma a_four (a : ℕ → ℕ) (ha0 : a 0 = 0)
    (hnext : ∀ n, a (n + 1) = nextValue a n) : a 4 = 15 := by
  have ha1 := a_one a ha0 hnext
  have ha3 := a_three a ha0 hnext
  rw [hnext 3, nextValue]
  split_ifs with h
  · exfalso
    have hmem := h.2 ⟨1, by omega⟩
    dsimp at hmem
    omega
  · omega

private lemma a_formula (a : ℕ → ℕ) (ha0 : a 0 = 0)
    (hnext : ∀ n, a (n + 1) = nextValue a n) :
    ∀ n, 3 ≤ n → a n = if n % 2 = 0 then 2 * n + 7 else n + 5 := by
  have ha1 := a_one a ha0 hnext
  have ha2 := a_two a ha0 hnext
  have ha3 := a_three a ha0 hnext
  have ha4 := a_four a ha0 hnext
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn5 : n < 5
    · interval_cases n
      · rw [ha3]; decide
      · rw [ha4]; decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      have hih : a (m + 4) = if (m + 4) % 2 = 0 then 2 * (m + 4) + 7 else (m + 4) + 5 :=
        ih (m + 4) (by omega) (by omega)
      rw [hnext (m + 4), nextValue]
      rcases Nat.mod_two_eq_zero_or_one (m + 5) with hev | hodd
      · have hm4 : (m + 4) % 2 = 1 := by omega
        simp only [hm4, hev, ↓reduceIte, (by decide : (1 : ℕ) ≠ 0)] at hih ⊢
        split_ifs with hcond
        · exfalso
          have hmem := hcond.2 ⟨1, by omega⟩
          change a 1 ≠ a (m + 4) - (m + 4 + 1) at hmem
          omega
        · omega
      · have hm4 : (m + 4) % 2 = 0 := by omega
        simp only [hm4, hodd, ↓reduceIte, (by decide : (1 : ℕ) ≠ 0)] at hih ⊢
        split_ifs with hcond
        · omega
        · exfalso
          apply hcond
          refine ⟨by omega, fun i => ?_⟩
          rcases i with ⟨i, hi⟩
          change a i ≠ a (m + 4) - (m + 4 + 1)
          by_cases hi3 : i < 3
          · interval_cases i <;> omega
          · have hiih := ih i (by omega) (by omega)
            split_ifs at hiih <;> omega

private lemma numerator_ge_seven {n : ℕ} (hn : 7 ≤ n) :
    numerator n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rfl

end OMA.P_oeis_a386969

open OMA.S_oeis_a386969 OMA.P_oeis_a386969 in
theorem OMA.solution : type_of% @OMA.S_oeis_a386969.main := by
  intro a ha0 hnext
  have hform := a_formula a ha0 hnext
  refine ⟨hform, ?_⟩
  have ha1 := a_one a ha0 hnext
  have ha2 := a_two a ha0 hnext
  have ha3 := a_three a ha0 hnext
  have ha4 := a_four a ha0 hnext
  have ha5 : a 5 = 10 := by
    have h := hform 5 (by omega)
    dsimp at h
    exact h
  have ha6 : a 6 = 19 := by
    have h := hform 6 (by omega)
    dsimp at h
    exact h
  intro n
  by_cases hn7 : n < 7
  · interval_cases n <;>
      simp [lag, numerator,
        ha0, ha1, ha2, ha3, ha4, ha5, ha6]
  · rw [numerator_ge_seven (by omega)]
    simp only [lag]
    rw [hform n (by omega), hform (n - 2) (by omega), hform (n - 4) (by omega)]
    split_ifs <;> omega
