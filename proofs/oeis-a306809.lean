import OMAStatements.S_oeis_a306809
import Mathlib

open OMA.S_oeis_a306809

namespace P306809

def T (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * f k

lemma pascal (f : ℕ → ℤ) (n : ℕ) : T f (n + 1) = T f n + T (fun k => f (k + 1)) n := by
  simp only [T]
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  have h : ∑ x ∈ Finset.range (n + 1), (n.choose x.succ : ℤ) * f (x + 1) + f 0 =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * f k := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun k => (n.choose k : ℤ) * f k)]
    simp
  rw [← h]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  ring

def A : ℕ → ℕ → ℤ
  | 0, n => a n
  | j + 1, n => A j (n + 1) - A j n

lemma A_eq : ∀ j n, A j n = T (fun k => (b (k + j) : ℤ)) n
  | 0, n => by simp [A, T, a]
  | j + 1, n => by
    rw [A, A_eq j, A_eq j, pascal]
    simp only [add_sub_cancel_left, add_assoc, add_comm 1 j]

lemma bd (k : ℕ) : (b (k + 6) : ℤ) - 2 * b (k + 3) + b k = if k = 0 then 1 else 0 := by
  rcases k with _ | j
  · simp [b]
  · have : b (j + 1 + 6) + b (j + 1) = 2 * b (j + 1 + 3) := by
      simp only [b, show j + 1 + 6 = (j + 6) + 1 by omega, show j + 1 + 3 = (j + 3) + 1 by omega]
      split_ifs <;> omega
    simp only [Nat.add_one_ne_zero, if_false]
    have h2 := congrArg (fun x : ℕ => (x : ℤ)) this
    push_cast at h2
    linear_combination h2

lemma key (n : ℕ) : A 6 n - 2 * A 3 n + A 0 n = 1 := by
  rw [A_eq, A_eq, A_eq]
  simp only [T, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have : ∀ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * (b (k + 6) : ℤ) -
      2 * ((n.choose k : ℤ) * (b (k + 3) : ℤ)) + (n.choose k : ℤ) * (b k : ℤ) =
      if k = 0 then 1 else 0 := by
    intro k _
    have h := bd k
    split_ifs at h ⊢ with hk
    · subst hk; simp only [Nat.choose_zero_right, Nat.cast_one]; linear_combination h
    · linear_combination (n.choose k : ℤ) * h
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  simp

end P306809

theorem OMA.solution : type_of% @OMA.S_oeis_a306809.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have h0 := P306809.key m
  have h1 := P306809.key (m + 1)
  simp only [P306809.A] at h0 h1
  simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega,
    show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m by omega]
  ring_nf at h0 h1 ⊢
  linear_combination h1 - h0
