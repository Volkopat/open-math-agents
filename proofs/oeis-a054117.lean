import OMAStatements.S_oeis_a054117

namespace OMA.S_oeis_a054117

open Finset

lemma double_sum (f : ℕ → ℕ) (h : ℕ) :
    ∑ k ∈ range (h + 1), ∑ j ∈ range (k + 1), f j = ∑ j ∈ range (h + 1), (h + 1 - j) * f j := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun j => (h + 1 + 1 - j) * f j)]
    rw [show h + 1 + 1 - (h + 1) = 1 by omega, one_mul]
    rw [sum_range_succ (fun j => f j) (h + 1)]
    have : ∑ j ∈ range (h + 1), (h + 1 + 1 - j) * f j =
        ∑ j ∈ range (h + 1), (h + 1 - j) * f j + ∑ j ∈ range (h + 1), f j := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun j hj => ?_
      rw [show h + 1 + 1 - j = (h + 1 - j) + 1 by simp at hj; omega]
      ring
    rw [this]
    ring

lemma sum_mul_fact (h : ℕ) : ∑ i ∈ range (h + 1), (i + 1) * (i + 1).factorial + 1 = (h + 2).factorial := by
  induction h with
  | zero => simp [Nat.factorial]
  | succ h ih =>
    rw [sum_range_succ, add_right_comm, ih, Nat.factorial_succ (h + 2)]
    ring

lemma r_eq : ∀ h, r h = (h + 1).factorial := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    cases h with
    | zero => simp [r]
    | succ h =>
      rw [r]
      have e : ∑ k ∈ range (h + 1), ∑ j ∈ range (k + 1), r (h - j) =
          ∑ k ∈ range (h + 1), ∑ j ∈ range (k + 1), (h - j + 1).factorial := by
        exact sum_congr rfl fun k _ => sum_congr rfl fun j _ => ih _ (by omega)
      rw [e, double_sum (fun j => (h - j + 1).factorial) h]
      have e2 : ∑ j ∈ range (h + 1), (h + 1 - j) * (h - j + 1).factorial =
          ∑ i ∈ range (h + 1), (i + 1) * (i + 1).factorial := by
        rw [← sum_range_reflect]
        apply sum_congr rfl
        intro i hi
        have : i < h + 1 := mem_range.mp hi
        rw [show h + 1 - (h + 1 - 1 - i) = i + 1 by omega,
          show h - (h + 1 - 1 - i) + 1 = i + 1 by omega]
      rw [e2, add_comm, sum_mul_fact]

lemma icc_sum (g : ℕ → ℕ) (k : ℕ) : ∑ j ∈ Icc 1 k, g j = ∑ i ∈ range k, g (1 + i) := by
  rw [show Icc 1 k = Ico 1 (k + 1) by ext x; simp [Nat.lt_succ_iff], Finset.sum_Ico_eq_sum_range]
  simp

lemma a_diff (n : ℕ) (hn : 4 ≤ n) : a n = a (n - 1) + (n.factorial : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h1 : T (m + 4) (m + 2) = r (m + 3) + T (m + 3) (m + 1) := by
    simp only [T, show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega, if_false, icc_sum]
    rw [sum_range_succ', add_comm]
    congr 1
    exact sum_congr rfl fun i _ => by congr 1; omega
  simp only [a, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 1 = m + 3 by omega, h1, r_eq]
  push_cast
  ring

theorem solution_main : ∀ n : ℕ, 5 ≤ n →
    a n - ((n : ℤ) + 1) * a (n - 1) + (n : ℤ) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have d1 := a_diff (m + 5) (by omega)
  have d2 := a_diff (m + 4) (by omega)
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 4 - 1 = m + 3 by omega,
    show m + 5 - 2 = m + 3 by omega] at d1 d2 ⊢
  rw [d1, d2, Nat.factorial_succ (m + 4)]
  push_cast
  ring

end OMA.S_oeis_a054117

theorem OMA.solution : type_of% @OMA.S_oeis_a054117.main := OMA.S_oeis_a054117.solution_main
