import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2

-- Credit: @xlh1551. The cutoff of 132 comes from the parent reduction by @Twalways.
-- Checking all nine thousand starting values also covers its thirteen residue classes.
open CollatzConjecture

namespace OMA.FiniteCollatzDescent

private def fallsBelow (bound : ℕ) : ℕ → ℕ → Bool
  | 0, x => decide (x < bound)
  | k + 1, x => if x < bound then true else fallsBelow bound k (collatzStep x)

private theorem fallsBelow_sound (bound : ℕ) (k x : ℕ) (h : fallsBelow bound k x = true) :
    ∃ i ≤ k, collatzStep^[i] x < bound := by
  induction k generalizing x with
  | zero => exact ⟨0, Nat.le_refl _, of_decide_eq_true h⟩
  | succ k ih =>
    by_cases hx : x < bound
    · exact ⟨0, Nat.zero_le _, hx⟩
    · obtain ⟨i, hik, hi⟩ := ih (collatzStep x) (by simpa [fallsBelow, hx] using h)
      exact ⟨i + 1, Nat.succ_le_succ hik, hi⟩

private def checkRow (q : ℕ) : Bool :=
  (List.range 100).all fun r => fallsBelow (1000 + 100 * q + r) 132 (1000 + 100 * q + r)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem rowsChecked : (List.range 90).all checkRow = true := by decide +kernel

/-- Every start in this interval descends within the same finite step bound. -/
theorem descendsWithin (n : ℕ) (hn : 1000 ≤ n) (hn' : n < 10000) :
    ∃ i ≤ 132, collatzStep^[i] n < n := by
  let q := (n - 1000) / 100
  let r := (n - 1000) % 100
  have hq : q < 90 := by dsimp [q]; omega
  have hr : r < 100 := Nat.mod_lt _ (by decide)
  have hx : 1000 + 100 * q + r = n := by dsimp [q, r]; omega
  have hrow := List.all_eq_true.mp rowsChecked q (List.mem_range.mpr hq)
  have hcell := List.all_eq_true.mp hrow r (List.mem_range.mpr hr)
  change fallsBelow (1000 + 100 * q + r) 132 (1000 + 100 * q + r) = true at hcell
  rw [hx] at hcell
  exact fallsBelow_sound n 132 n hcell

end OMA.FiniteCollatzDescent

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2.H1 := by
  intro n hn hn' _
  obtain ⟨i, _, hi⟩ := OMA.FiniteCollatzDescent.descendsWithin n hn hn'
  exact ⟨i, hi⟩
