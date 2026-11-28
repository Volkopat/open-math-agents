import OMAStatements.S_oeis_a285802
import Mathlib
open OMA.S_oeis_a285802
theorem hasSeven_of (x : ℕ) (h : x % 10 = 7 ∨ (x / 10) % 10 = 7) : HasSeven x := by
  unfold HasSeven
  have hx : 0 < x := by omega
  rw [Nat.digits_def' (by norm_num) hx]
  rcases h with h | h
  · simp [h]
  · have hx' : 0 < x / 10 := by omega
    rw [Nat.digits_def' (by norm_num) hx']
    simp [h]

theorem hasSeven_mul_ten (x : ℕ) (h : HasSeven x) : HasSeven (x * 10) := by
  unfold HasSeven at *
  have hx : 0 < x := by
    rcases Nat.eq_zero_or_pos x with rfl | h'
    · simp at h
    · exact h'
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have : x * 10 / 10 = x := by omega
  simp [this, h]

theorem key0 : ∀ r < 100, r % 10 ≠ 0 → ∃ k < 36, 1 ≤ k ∧
    ((k * r) % 10 = 7 ∨ ((k * r) / 10) % 10 = 7) := by decide +kernel

theorem key (r : ℕ) (hr : r < 100) (h : r % 10 ≠ 0) : ∃ k, 1 ≤ k ∧ k ≤ 35 ∧
    ((k * r) % 10 = 7 ∨ ((k * r) / 10) % 10 = 7) := by
  obtain ⟨k, hk, h1, h2⟩ := key0 r hr h
  exact ⟨k, h1, by omega, h2⟩

theorem part1 : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ 35 ∧ HasSeven (k * n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h10 : n % 10 = 0
    · obtain ⟨m, rfl⟩ : ∃ m, n = m * 10 := ⟨n / 10, by omega⟩
      obtain ⟨k, hk1, hk2, hk⟩ := ih m (by omega) (by omega)
      exact ⟨k, hk1, hk2, by rw [← mul_assoc]; exact hasSeven_mul_ten _ hk⟩
    · obtain ⟨k, hk1, hk2, hk⟩ := key (n % 100) (Nat.mod_lt _ (by norm_num)) (by omega)
      refine ⟨k, hk1, hk2, hasSeven_of _ ?_⟩
      have e : k * n % 100 = k * (n % 100) % 100 := by simp [Nat.mul_mod]
      generalize k * n = x at e ⊢
      generalize k * (n % 100) = y at e hk
      omega

theorem OMA.solution : type_of% @OMA.S_oeis_a285802.main := by
  refine ⟨part1, ?_, ?_⟩
  · intro k hk1 hk2
    unfold HasSeven
    interval_cases k <;> norm_num
  · unfold HasSeven
    norm_num
