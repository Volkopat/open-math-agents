import OMAStatements.S_oeis_a309054
import Mathlib

open OMA.S_oeis_a309054


theorem a3 (m : ℕ) : a (3 * m) = 1 := by
  rcases m with _ | m
  · simp [a]
  · rw [show 3 * (m + 1) = (3 * m + 1) + 2 by ring, a]
    rw [if_pos (by omega)]

theorem a3p2 (m : ℕ) : a (3 * m + 2) = 2 * a m := by
  rw [show 3 * m + 2 = 3 * m + 2 by rfl, a]
  rw [if_neg (by omega), if_pos (by omega)]
  congr 2; omega

theorem a3p1 (m : ℕ) : a (3 * m + 1) = 2 * a (m + 1) := by
  rcases m with _ | m
  · simp [a]
  · rw [show 3 * (m + 1) + 1 = (3 * m + 2) + 2 by ring, a]
    rw [if_neg (by omega), if_neg (by omega)]
    congr 2; omega

theorem peel (M : ℕ) (f : ℤ → ℕ) :
    ∑ n ∈ Finset.Ico (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ), f n =
      ∑ n ∈ Finset.Ico (-(M : ℤ)) M, f n + f (-((M : ℤ) + 1)) + f M := by
  have e : Finset.Ico (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
      insert (-((M : ℤ) + 1)) (insert (M : ℤ) (Finset.Ico (-(M : ℤ)) M)) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; push_cast; omega
  rw [e, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ico]; omega),
    Finset.sum_insert (by simp only [Finset.mem_Ico]; omega)]
  ring

noncomputable def T (M : ℕ) : ℕ := ∑ n ∈ Finset.Ico (-(M : ℤ)) M, (aZ n + 1)

theorem peel' (M : ℕ) : T (M + 1) = T M + (a (M + 1) + 1) + (a M + 1) := by
  unfold T
  rw [peel M (fun n => aZ n + 1)]
  have e1 : aZ (-((M : ℤ) + 1)) = a (M + 1) := by
    unfold aZ; congr 1
  have e2 : aZ (M : ℤ) = a M := by
    simp [aZ]
  rw [e1, e2]

theorem key (m : ℕ) : T (3 * m) = 4 * T m := by
  induction m with
  | zero => simp [T]
  | succ m ih =>
    rw [show 3 * (m + 1) = (3 * m + 2) + 1 by ring, peel', show 3 * m + 2 = (3 * m + 1) + 1 by ring,
      peel', peel', ih, peel', show 3 * m + 1 + 1 + 1 = 3 * (m + 1) by ring,
      show 3 * m + 1 + 1 = 3 * m + 2 by ring, a3, a3, a3p1, a3p2]
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a309054.main := by
  intro m
  have h := key m
  unfold T at h
  push_cast at h
  exact h
