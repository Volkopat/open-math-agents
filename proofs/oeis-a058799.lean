import OMAStatements.S_oeis_a058799
import Mathlib

namespace A058799Proof

open OMA.S_oeis_a058799

lemma run_succ (n : ℕ) : running (n + 1) = ((running n).1 + ((n : ℤ) + 1) * (running n).2,
    (running n).2 + ((running n).1 + ((n : ℤ) + 1) * (running n).2)) := by
  rw [running]

lemma sum_eq (n : ℕ) : ∑ j ∈ Finset.range (n + 1), (running j).1 = (running n).2 := by
  induction n with
  | zero => simp [running]
  | succ k ih => rw [Finset.sum_range_succ, ih, run_succ]

lemma T_rec (n : ℕ) :
    (running (n + 1 + 1)).2 = ((n : ℤ) + 4) * (running (n + 1)).2 - (running n).2 := by
  rw [run_succ (n + 1), run_succ n]
  dsimp only
  push_cast
  ring

lemma both (n : ℕ) : frieze 2 n = (running n).2 ∧ frieze 2 (n + 1) = (running (n + 1)).2 := by
  induction n with
  | zero =>
    constructor
    · simp [frieze, running]
    · rw [run_succ 0]
      simp [frieze, running]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hf : frieze 2 (k + 1 + 1) = ((k : ℤ) + (2 : ℕ) + 2) * frieze 2 (k + 1) - frieze 2 k := by
      rw [frieze]
    rw [hf, T_rec k, ← ih.1, ← ih.2]
    push_cast
    ring

end A058799Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a058799.main := by
  intro n
  rw [A058799Proof.sum_eq]
  exact (A058799Proof.both n).1
