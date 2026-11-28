import OMAStatements.S_oeis_a131626
import Mathlib

open OMA.S_oeis_a131626

theorem OMA.solution : type_of% @OMA.S_oeis_a131626.main := by
  intro x hx
  have c3 : ∀ N : ℕ, 3 ∣ N → 3 < N → ¬ Nat.Prime N := by
    intro N hd hl hp
    rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega
  have p0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have p1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  have p2 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  have p3 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
  have p8 : Nat.nth Nat.Prime 8 = 23 := by
    have h : Nat.count Nat.Prime 23 = 8 := by decide
    rw [← h]; exact Nat.nth_count (by norm_num)
  have p9 : Nat.nth Nat.Prime 9 = 29 := by
    have h : Nat.count Nat.Prime 29 = 9 := by decide
    rw [← h]; exact Nat.nth_count (by norm_num)
  have hx3 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases hx3 with h | h | h
  · refine ⟨0, ?_⟩
    rw [p0, p1]; exact c3 _ (by omega) (by omega)
  · refine ⟨8, ?_⟩
    rw [p8, p9]; exact c3 _ (by omega) (by omega)
  · refine ⟨2, ?_⟩
    rw [p2, p3]; exact c3 _ (by omega) (by omega)
