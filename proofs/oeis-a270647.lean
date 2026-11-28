import OMAStatements.S_oeis_a270647
import Mathlib

/-!
# A270647: dropping the first letter of the A270643 word gives the A270647 word

Write C(k) for the word built from 1, 2, 2, 1 after k steps and D(k) for the word built from
2, 2, 1, 2 after k steps. The tail of C(1) = 1, 2, 2, 1, 2 is D(0) = 2, 2, 1, 2. If the tail of
C(k+1) is D(k), then letter k+2 of C(k+1) is letter k+1 of D(k) and the last letters agree
(D(k) is not empty), so step k+2 of C appends exactly the block that step k+1 of D appends, and
the tail of C(k+2) is D(k+1). Then A270643(n+1) = letter n+1 of C(n+1) = letter n of D(n) = a(n).
-/

namespace OMA.P270647

open OMA.S_oeis_a270647

lemma build_succ (w : List ℕ) (k : ℕ) :
    build w (k + 1) =
      build w k ++ List.replicate ((build w k).getD k 0) (opp ((build w k).getLastD 0)) := rfl

lemma length_build (w : List ℕ) (k : ℕ) : w.length ≤ (build w k).length := by
  induction k with
  | zero => exact le_refl _
  | succ k ih =>
    rw [build_succ, List.length_append]
    omega

lemma key (k : ℕ) : (build [1, 2, 2, 1] (k + 1)).tail = build [2, 2, 1, 2] k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlen : 4 ≤ (build [2, 2, 1, 2] k).length := length_build [2, 2, 1, 2] k
    obtain ⟨y, s, hys⟩ : ∃ y s, build [2, 2, 1, 2] k = y :: s := by
      cases h : build [2, 2, 1, 2] k with
      | nil => rw [h] at hlen; simp at hlen
      | cons y s => exact ⟨y, s, rfl⟩
    obtain ⟨x, t, hxt⟩ : ∃ x t, build [1, 2, 2, 1] (k + 1) = x :: t := by
      cases h : build [1, 2, 2, 1] (k + 1) with
      | nil => rw [h] at ih; rw [← ih] at hlen; simp at hlen
      | cons x t => exact ⟨x, t, rfl⟩
    rw [hxt, List.tail_cons, hys] at ih
    rw [build_succ [1, 2, 2, 1] (k + 1), build_succ [2, 2, 1, 2] k, hxt, hys, ih]
    simp

theorem sol : type_of% @OMA.S_oeis_a270647.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hlen : 4 ≤ (build [2, 2, 1, 2] (m + 1)).length := length_build [2, 2, 1, 2] (m + 1)
  obtain ⟨x, t, hxt⟩ : ∃ x t, build [1, 2, 2, 1] (m + 1 + 1) = x :: t := by
    cases h : build [1, 2, 2, 1] (m + 1 + 1) with
    | nil =>
      have h2 := key (m + 1)
      rw [h] at h2
      rw [← h2] at hlen
      simp at hlen
    | cons x t => exact ⟨x, t, rfl⟩
  have h2 := key (m + 1)
  rw [hxt, List.tail_cons] at h2
  unfold a A270643
  rw [hxt, ← h2]
  simp

end OMA.P270647

theorem OMA.solution : type_of% @OMA.S_oeis_a270647.main := OMA.P270647.sol

