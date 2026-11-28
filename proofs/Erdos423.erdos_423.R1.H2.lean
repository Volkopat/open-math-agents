import OMAReductions.R_Erdos423_erdos_423_R1

-- Step Erdos423.erdos_423.R1.H2: hypothesis H2 of reduction Erdos423.erdos_423.R1
-- Credit: @mburv
-- The argument is the upstream proof of erdos_423.variants.nondecreasing (formal-conjectures,
-- Apache-2.0), restated here for the step.

open Erdos423

theorem OMA.solution : OMA.R_Erdos423_erdos_423_R1.H2 := by
  intro a ⟨ha1, ha2, hk⟩ n m hn hnm
  have step : ∀ k, 1 ≤ k → a k + 1 ≤ a (k + 1) := by
    intro k hk1
    rcases Nat.lt_or_ge k 2 with h | h
    · obtain rfl : k = 1 := by omega
      rw [ha1, ha2]
    · simpa using (hk (k + 1) (by omega)).2.1
  have ge : ∀ k, 1 ≤ k → k ≤ a k := by
    intro k hk1
    induction k with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [ha1]
      · have := step j hj; have := ih hj; omega
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
    have h1 := step m (by omega)
    have h2 := ge m (by omega)
    omega
