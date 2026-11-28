import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3

-- Step CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R3.H1: hypothesis H1 of reduction
-- CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R3.
-- Written with Claude Code (AI-assisted).
-- Proof by reflection: a fuelled Boolean search iterates the Collatz map until the value drops
-- below the start; one soundness lemma, and the kernel checks [1000, 100000) in 198 blocks.

namespace OMA.CollatzR3H1

open CollatzConjecture

def stepB (m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else 3 * m + 1

theorem stepB_eq (m : ℕ) : stepB m = collatzStep m := by
  unfold stepB
  split
  · rw [OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3.step_even (by assumption)]
  · rw [OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3.step_odd (by omega)]

/-- `runB f m n = true` certifies that some iterate of the Collatz map from `m` is below `n`. -/
def runB : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, m, n => if m < n then true else runB f (stepB m) n

theorem runB_sound : ∀ (f m n : ℕ), runB f m n = true → ∃ i : ℕ, collatzStep^[i] m < n := by
  intro f
  induction f with
  | zero => intro m n h; simp [runB] at h
  | succ f ih =>
    intro m n h
    simp only [runB] at h
    split at h
    · exact ⟨0, by simpa⟩
    · obtain ⟨i, hi⟩ := ih _ _ h
      refine ⟨i + 1, ?_⟩
      rw [Function.iterate_succ_apply, ← stepB_eq]
      exact hi

def classes : List ℕ :=
  [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255]

def blockOK (a : ℕ) : Bool :=
  (List.range' a 500).all fun n => !(classes.contains (n % 256)) || runB 1000 n n

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem allBlocks : ∀ x : Fin 198, blockOK (1000 + 500 * x.val) = true := by
  intro x
  fin_cases x <;> decide +kernel

end OMA.CollatzR3H1

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3.H1 := by
  intro n h1 h2 hmod
  have hb := OMA.CollatzR3H1.allBlocks ⟨(n - 1000) / 500, by omega⟩
  have hmem : n ∈ List.range' (1000 + 500 * ((n - 1000) / 500)) 500 := by
    rw [List.mem_range'_1]
    omega
  have hn := List.all_eq_true.mp hb n hmem
  have hc : OMA.CollatzR3H1.classes.contains (n % 256) = true := by
    simpa [OMA.CollatzR3H1.classes] using hmod
  rw [hc] at hn
  exact OMA.CollatzR3H1.runB_sound 1000 n n (by simpa using hn)
