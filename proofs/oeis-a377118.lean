import OMAStatements.S_oeis_a377118
import Mathlib

open OMA.S_oeis_a377118

lemma a0 : a 0 = 0 := by decide
lemma a1 : a 1 = 1 := by decide
lemma a2 : a 2 = 2 := by decide

lemma nth0 : Nat.nth (fun n => 2 ∣ a n) 0 = 0 := by
  have h : (fun n => 2 ∣ a n) 0 := by
    show 2 ∣ a 0
    rw [a0]; exact dvd_zero 2
  have := Nat.nth_count (p := fun n => 2 ∣ a n) h
  simpa using this

lemma nth1 : Nat.nth (fun n => 2 ∣ a n) 1 = 2 := by
  have h : (fun n => 2 ∣ a n) 2 := by
    show 2 ∣ a 2
    rw [a2]
  have h2 := Nat.nth_count (p := fun n => 2 ∣ a n) h
  have hc : Nat.count (fun n => 2 ∣ a n) 2 = 1 := by
    rw [Nat.count_succ, Nat.count_succ, Nat.count_zero]
    simp [a0, a1]
  rw [hc] at h2
  exact h2

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377118.main) := by
  intro h
  have h2 := (h 2 Nat.prime_two).2 [1] (by simp [displayed])
  obtain ⟨phase, hph⟩ := h2.1
  have h0 := hph 0
  unfold gap at h0
  rw [nth0, nth1] at h0
  simp [Nat.mod_one] at h0
