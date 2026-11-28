import OMAStatements.S_oeis_a377115
import Mathlib

/-!
Disproof of the OEIS A377115 conjecture: the displayed block for p = 7 is wrong.
The argument follows the accepted proof of the template entry OEIS A377118 (a displayed block
contradicted by the first gap), with the prime 7 in place of 2.
The terms a(1), ..., a(7) are not divisible by 7 while a(0) = 0 and a(8) = 295680 are, so the
first gap is 8, a value that does not occur in the displayed block for p = 7.
-/

namespace A377115

open OMA.S_oeis_a377115

lemma nth0 : Nat.nth (fun n => 7 ∣ a n) 0 = 0 := by
  have h : (fun n => 7 ∣ a n) 0 := by
    show 7 ∣ a 0
    decide
  simpa using Nat.nth_count (p := fun n => 7 ∣ a n) h

lemma nth1 : Nat.nth (fun n => 7 ∣ a n) 1 = 8 := by
  have h : (fun n => 7 ∣ a n) 8 := by
    show 7 ∣ a 8
    decide +kernel
  have h2 := Nat.nth_count (p := fun n => 7 ∣ a n) h
  have hc : Nat.count (fun n => 7 ∣ a n) 8 = 1 := by decide +kernel
  rw [hc] at h2
  exact h2

end A377115

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377115.main) := by
  intro h
  have h2 := (h 7 (by norm_num)).2 [14, 4, 4, 2, 12, 1, 11, 5, 1, 18]
    (by simp [OMA.S_oeis_a377115.displayed])
  obtain ⟨phase, hph⟩ := h2.1
  have h0 := hph 0
  unfold OMA.S_oeis_a377115.gap at h0
  rw [A377115.nth0, A377115.nth1] at h0
  have hl : ([14, 4, 4, 2, 12, 1, 11, 5, 1, 18] : List ℕ).length = 10 := rfl
  rw [hl] at h0
  have hlt : (0 + phase) % 10 < 10 := Nat.mod_lt _ (by norm_num)
  generalize (0 + phase) % 10 = r at h0 hlt
  interval_cases r <;> simp at h0
