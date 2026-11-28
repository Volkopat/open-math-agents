import OMAStatements.S_oeis_a001045
import Mathlib

-- Problem: A001045: Jacobsthal sequence (or Jacobsthal numbers): a(n) = a(n-1) + 2*a(n-2), with a(0) = 0, a(1) = 1; also a(n) = nearest integer to 2^n
-- Upstream: formal-conjectures statements/oeis-a001045.lean:0 (declaration OMA.S_oeis_a001045.main)
-- Credit: @Salofe (the owner of the agent is credited as the solver)

open OMA.S_oeis_a001045 in
theorem OMA.solution : type_of% @OMA.S_oeis_a001045.main := by
  -- Binet-type identity: 3 a(n) = 2^n - (-1)^n.
  have h : ∀ n, 3 * a n = 2 ^ n - (-1) ^ n ∧ 3 * a (n + 1) = 2 ^ (n + 1) - (-1) ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp [a]
    | succ n ih => exact ⟨ih.2, by rw [a]; linear_combination ih.2 + 2 * ih.1⟩
  have hA : ∀ n, A ^ (n + 1) = Matrix.of fun i j => if i = j then 2 * a n else a (n + 1) := by
    intro n
    induction n with
    | zero => ext i j; simp [A, a]
    | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, A, a] <;> ring
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · have hx : ((2 ^ n : ℕ) : ℤ) = 2 ^ n := by push_cast; rfl
    have h3 := Nat.Ioc_filter_dvd_card_eq_div (2 * 2 ^ n - 1) 3
    have hp := Nat.one_le_two_pow (n := n)
    rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le (2 ^ n)) (by omega), Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (by simp)),
      Nat.Ioc_filter_dvd_card_eq_div] at h3
    rw [pow_succ, show Finset.Ioo (2 ^ n) (2 ^ n * 2) = Finset.Ioc (2 ^ n) (2 * 2 ^ n - 1) by
      ext; simp; omega]
    have := (h n).1
    rcases neg_one_pow_eq_or ℤ n with e | e <;> rw [e, ← hx] at this <;> omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have := h k
    rw [hA]
    refine ⟨by simp [Matrix.trace]; ring, fun i j hij => by simp [hij], fun i => ?_⟩
    rcases Nat.even_or_odd k with e | e <;> simp [e.neg_one_pow, Nat.even_add_one, e, pow_succ] at this ⊢ <;> linarith
