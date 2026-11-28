import OMAStatements.S_oeis_a097967
import Mathlib

open OMA.S_oeis_a097967 in
theorem OMA.solution : type_of% @OMA.S_oeis_a097967.main := by
  have b (f : ℕ → ℤ) (n : ℕ) : ∑ k ∈ Finset.range (n + 1), f k = f 0 + ∑ k ∈ Finset.Icc 1 n, f k := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]; ring
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → ℤ, ∀ n, Q n = ∑ k ∈ Finset.range (n + 1), (n.descFactorial k : ℤ) :=
    ⟨_, fun _ => rfl⟩
  have q (n : ℕ) : Q (n + 1) = (n + 1) * Q n + 1 := by
    rw [hQ, hQ, Finset.sum_range_succ' _ (n + 1), Finset.mul_sum]
    simp only [Nat.succ_descFactorial_succ, Nat.descFactorial_zero]
    push_cast
    rfl
  have ha (n : ℕ) : a n = Q n + 2 ^ n - 2 := by
    have h1 := b (fun k => (n.descFactorial k : ℤ)) n
    have h2 := b (fun k => (n.choose k : ℤ)) n
    have h3 : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) = 2 ^ n := mod_cast Nat.sum_range_choose n
    simp only [Nat.descFactorial_zero, Nat.choose_zero_right, Nat.cast_one] at h1 h2
    rw [hQ, a, Finset.sum_add_distrib]
    linarith
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [Nat.reduceSubDiff, Nat.add_sub_cancel, ha, q]
  push_cast
  ring
