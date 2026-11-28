import OMAStatements.S_oeis_a057030
import Mathlib.Tactic

open OMA.S_oeis_a057030

namespace ReversingBlocks

private lemma translated (m c i : ℕ) :
    sourcePosition m (c+1) (i+1) = sourcePosition m c i + 1 := by
  by_cases h : i < c
  · have h' : i+1 < c+1 := by omega
    simp [sourcePosition, h, h']
  · have h' : ¬ i+1 < c+1 := by omega
    have offset : i+1-(c+1) = i-c := by omega
    simp only [sourcePosition, if_neg h, if_neg h', offset]
    omega

private lemma shifted (r i : ℕ) :
    afterStages 1 r (i+1) = afterStages 0 r i + 1 := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
    simp only [afterStages, Nat.add_zero, translated, ih]

private lemma stable (n : ℕ) : afterStages 1 (n+1) n = afterStages 1 n n := by
  simp [afterStages, sourcePosition, show n < n+1+1 by omega]

end ReversingBlocks

theorem OMA.solution : type_of% @OMA.S_oeis_a057030.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  change afterStages 0 (k+1) k = afterStages 1 (k+1+1) (k+1) - 1
  rw [ReversingBlocks.stable, ReversingBlocks.shifted]
  omega
