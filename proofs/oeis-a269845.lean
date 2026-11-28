import OMAStatements.S_oeis_a269845
import Mathlib

open OMA.S_oeis_a269845


theorem sum_pairs (f : ℕ → ℕ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n), f k = ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

theorem sq_sum (n : ℕ) : 6 * ∑ i ∈ Finset.range n, (i + 1) ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

theorem row (n : ℕ) : 3 * rowSum n = n * (n + 1) * (2 * n + 1) := by
  unfold rowSum
  rw [sum_pairs]
  have h1 : ∀ i ∈ Finset.range n, T n (2 * i) + T n (2 * i + 1) = (n - i) ^ 2 + (i + 1) ^ 2 := by
    intro i hi
    unfold T
    rw [if_neg (by omega), if_pos (by omega)]
    congr 2
    · omega
    · omega
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  have h2 : ∑ i ∈ Finset.range n, (n - i) ^ 2 = ∑ i ∈ Finset.range n, (i + 1) ^ 2 := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    congr 1
    omega
  rw [h2]
  have := sq_sum n
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a269845.main := by
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · have h := row (2 * m - 1)
    obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (r + 1) - 1 = 2 * r + 1 by omega] at h ⊢
    unfold A100157
    have e : 16 * (r + 1) ^ 3 - 12 * (r + 1) ^ 2 + 2 * (r + 1) = (2 * r + 1) * (2 * r + 1 + 1) * (2 * (2 * r + 1) + 1) := by
      have : 12 * (r + 1) ^ 2 ≤ 16 * (r + 1) ^ 3 := by nlinarith
      zify [this]
      push_cast
      ring
    rw [e]
    omega
  · have h := row (2 * m)
    unfold A258582
    have e : 3 * (m * (2 * m + 1) * (4 * m + 1)) = 2 * m * (2 * m + 1) * (2 * (2 * m) + 1) / 2 * 3 := by
      rw [show 2 * m * (2 * m + 1) * (2 * (2 * m) + 1) = 2 * (m * (2 * m + 1) * (4 * m + 1)) by ring]
      omega
    omega
