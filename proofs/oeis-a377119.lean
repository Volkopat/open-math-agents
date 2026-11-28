import OMAStatements.S_oeis_a377119
import Mathlib

open OMA.S_oeis_a377119 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377119.main) := by
  intro h
  have h2 := h.2.1 0
  have hc : Nat.count (fun n => 2 ∣ a n) 3 = 1 := by decide
  have h3 : Nat.nth (fun n => 2 ∣ a n) 1 = 3 := by
    have := Nat.nth_count (p := fun n => 2 ∣ a n) (n := 3) (by decide)
    rwa [hc] at this
  have h0 : Nat.nth (fun n => 2 ∣ a n) 0 = 0 := Nat.nth_zero_of_zero (by decide)
  have e : gap 2 0 = 3 := by
    unfold gap
    rw [show (0 : ℕ) + 1 = 1 from rfl, h3, h0]
  rw [e] at h2
  exact absurd h2 (by decide)
