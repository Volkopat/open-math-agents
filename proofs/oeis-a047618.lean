import OMAStatements.S_oeis_a047618

-- Problem: OEIS A047618, numbers congruent to 0, 2, 5 mod 8.
-- Each block of 8 consecutive integers contains exactly 3 terms, so the count of terms below
-- 8k, 8k + 2, 8k + 5 is 3k, 3k + 1, 3k + 2, and Nat.nth_count gives a(3k+1) = 8k,
-- a(3k+2) = 8k + 2, a(3k+3) = 8k + 5. Both relations then follow by a case split on n mod 3.

namespace OMA.A047618
open OMA.S_oeis_a047618

def P (m : ℕ) : Prop := m % 8 = 0 ∨ m % 8 = 2 ∨ m % 8 = 5

instance : DecidablePred P := fun m => by unfold P; infer_instance

theorem shift_eq (k : ℕ) : (fun i => P (8 * k + i)) = P := by
  funext i; apply propext; simp only [P]; omega

theorem count_mul (k : ℕ) : Nat.count P (8 * k) = 3 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 8 * (k + 1) = 8 * k + 8 by ring, Nat.count_add, ih]
    simp only [shift_eq]
    have : Nat.count P 8 = 3 := by decide
    omega

theorem count_shift (k j : ℕ) : Nat.count P (8 * k + j) = 3 * k + Nat.count P j := by
  rw [Nat.count_add, count_mul]
  simp only [shift_eq]

theorem a_eq_nth (n : ℕ) : a n = Nat.nth P (n - 1) := by
  rfl

theorem v1 (k : ℕ) : a (3 * k + 1) = 8 * k := by
  rw [a_eq_nth, show 3 * k + 1 - 1 = 3 * k by omega]
  have h : Nat.count P (8 * k) = 3 * k := by simpa using count_shift k 0
  rw [← h]; exact Nat.nth_count (by simp [P])

theorem v2 (k : ℕ) : a (3 * k + 2) = 8 * k + 2 := by
  rw [a_eq_nth, show 3 * k + 2 - 1 = 3 * k + 1 by omega]
  have h : Nat.count P (8 * k + 2) = 3 * k + 1 := by
    rw [count_shift]; simp only [add_right_inj]; decide
  rw [← h]; exact Nat.nth_count (by simp [P])

theorem v3 (k : ℕ) : a (3 * k + 3) = 8 * k + 5 := by
  rw [a_eq_nth, show 3 * k + 3 - 1 = 3 * k + 2 by omega]
  have h : Nat.count P (8 * k + 5) = 3 * k + 2 := by
    rw [count_shift]; simp only [add_right_inj]; decide
  rw [← h]; exact Nat.nth_count (by simp [P])

theorem sum3 (n : ℕ) (hn : 1 ≤ n) : (a n : ℤ) + a (n + 1) + a (n + 2) = 8 * n - 1 := by
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 3 ∧ n = 3 * k + r + 1 := ⟨(n - 1) / 3, (n - 1) % 3, by omega, by omega⟩
  interval_cases r
  · rw [show 3 * k + 0 + 1 = 3 * k + 1 by ring, show 3 * k + 1 + 1 = 3 * k + 2 by ring,
      show 3 * k + 1 + 2 = 3 * k + 3 by ring, v1, v2, v3]
    push_cast; ring
  · rw [show 3 * k + 1 + 1 = 3 * k + 2 by ring, show 3 * k + 2 + 1 = 3 * k + 3 by ring,
      show 3 * k + 2 + 2 = 3 * (k + 1) + 1 by ring, v2, v3, v1]
    push_cast; ring
  · rw [show 3 * k + 2 + 1 = 3 * k + 3 by ring, show 3 * k + 3 + 1 = 3 * (k + 1) + 1 by ring,
      show 3 * k + 3 + 2 = 3 * (k + 1) + 2 by ring, v3, v1, v2]
    push_cast; ring

end OMA.A047618

theorem OMA.solution : type_of% @OMA.S_oeis_a047618.main := by
  refine ⟨OMA.A047618.sum3, by simpa using OMA.A047618.v1 0, by simpa using OMA.A047618.v2 0,
    by simpa using OMA.A047618.v3 0, ?_⟩
  intro n hn
  have h := OMA.A047618.sum3 (n - 2) (by omega)
  rw [show n - 2 + 1 = n - 1 by omega, show n - 2 + 2 = n by omega] at h
  push_cast [show 2 ≤ n by omega] at h ⊢
  linarith
