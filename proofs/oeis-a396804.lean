import OMAStatements.S_oeis_a396804
import Mathlib.Tactic

namespace OMA.P_oeis_a396804

open OMA.S_oeis_a396804

private lemma egfPrefix_1 : egfPrefix 1 = [0, 1] := by
  norm_num [egfPrefix, expSeq, compSeq, powSeq, mulSeq, Finset.sum_range_succ, Nat.factorial]

private lemma egfPrefix_2 : egfPrefix 2 = [0, 1, 1] := by
  norm_num [egfPrefix, egfPrefix_1, expSeq, compSeq, powSeq, mulSeq, Finset.sum_range_succ, Nat.factorial]

private lemma egfPrefix_3 : egfPrefix 3 = [0, 1, 1, 9 / 2] := by
  norm_num [egfPrefix, egfPrefix_2, expSeq, compSeq, powSeq, mulSeq, Finset.sum_range_succ, Nat.factorial]

private lemma egfPrefix_4 : egfPrefix 4 = [0, 1, 1, 9 / 2, 205 / 6] := by
  have hprev : egfPrefix 3 = [0, 1, 1, 9 / 2] := egfPrefix_3
  let f : ℕ → ℚ := fun k => ([0, 1, 1, 9 / 2] : List ℚ).getD k 0
  let p2 := compSeq f f
  let p4 := compSeq p2 p2
  have hp2_0 : p2 0 = 0 := by norm_num [p2, f, compSeq, powSeq, mulSeq, Finset.sum_range_succ]
  have hp2_1 : p2 1 = 1 := by norm_num [p2, f, compSeq, powSeq, mulSeq, Finset.sum_range_succ]
  have hp2_2 : p2 2 = 2 := by norm_num [p2, f, compSeq, powSeq, mulSeq, Finset.sum_range_succ]
  have hp2_3 : p2 3 = 11 := by norm_num [p2, f, compSeq, powSeq, mulSeq, Finset.sum_range_succ]
  have hp4_0 : p4 0 = 0 := by norm_num [p4, compSeq, powSeq, mulSeq, Finset.sum_range_succ, hp2_0]
  have hp4_1 : p4 1 = 1 := by norm_num [p4, compSeq, powSeq, mulSeq, Finset.sum_range_succ, hp2_0, hp2_1]
  have hp4_2 : p4 2 = 4 := by norm_num [p4, compSeq, powSeq, mulSeq, Finset.sum_range_succ, hp2_0, hp2_1, hp2_2]
  have hp4_3 : p4 3 = 30 := by norm_num [p4, compSeq, powSeq, mulSeq, Finset.sum_range_succ, hp2_0, hp2_1, hp2_2, hp2_3]
  have hexp : expSeq p4 3 = 205 / 6 := by
    norm_num [expSeq, powSeq, mulSeq, Finset.sum_range_succ, Nat.factorial, hp4_0, hp4_1, hp4_2, hp4_3]
  show egfPrefix 3 ++ [expSeq (compSeq (compSeq (fun k => (egfPrefix 3).getD k 0) (fun k => (egfPrefix 3).getD k 0)) (compSeq (fun k => (egfPrefix 3).getD k 0) (fun k => (egfPrefix 3).getD k 0))) 3] = _
  rw [hprev]
  change [0, 1, 1, 9 / 2] ++ [expSeq p4 3] = _
  rw [hexp]
  rfl

private lemma egfPrefix_5 : egfPrefix 5 = [0, 1, 1, 9 / 2, 205 / 6, 8201 / 24] := by
  have hprev : egfPrefix 4 = [0, 1, 1, 9 / 2, 205 / 6] := egfPrefix_4
  let f : ℕ → ℚ := fun k => ([0, 1, 1, 9 / 2, 205 / 6] : List ℚ).getD k 0
  let p2 := compSeq f f
  let p4 := compSeq p2 p2
  have hp2_0 : p2 0 = 0 := by norm_num [p2, f, compSeq, powSeq, mulSeq, Finset.sum_range_succ]
  have hp2_1 : p2 1 = 1 := by norm_num [p2, f, compSeq, powSeq, mulSeq, Finset.sum_range_succ]
  have hp2_2 : p2 2 = 2 := by norm_num [p2, f, compSeq, powSeq, mulSeq, Finset.sum_range_succ]
  have hp2_3 : p2 3 = 11 := by norm_num [p2, f, compSeq, powSeq, mulSeq, Finset.sum_range_succ]
  have hp2_4 : p2 4 = 551 / 6 := by norm_num [p2, f, compSeq, powSeq, mulSeq, Finset.sum_range_succ]
  have hp4_0 : p4 0 = 0 := by norm_num [p4, compSeq, powSeq, mulSeq, Finset.sum_range_succ, hp2_0]
  have hp4_1 : p4 1 = 1 := by norm_num [p4, compSeq, powSeq, mulSeq, Finset.sum_range_succ, hp2_0, hp2_1]
  have hp4_2 : p4 2 = 4 := by norm_num [p4, compSeq, powSeq, mulSeq, Finset.sum_range_succ, hp2_0, hp2_1, hp2_2]
  have hp4_3 : p4 3 = 30 := by norm_num [p4, compSeq, powSeq, mulSeq, Finset.sum_range_succ, hp2_0, hp2_1, hp2_2, hp2_3]
  have hp4_4 : p4 4 = 905 / 3 := by
    norm_num [p4, compSeq, powSeq, mulSeq, Finset.sum_range_succ, hp2_0, hp2_1, hp2_2, hp2_3, hp2_4]
  have hexp : expSeq p4 4 = 8201 / 24 := by
    norm_num [expSeq, powSeq, mulSeq, Finset.sum_range_succ, Nat.factorial, hp4_0, hp4_1, hp4_2, hp4_3, hp4_4]
  show egfPrefix 4 ++ [expSeq (compSeq (compSeq (fun k => (egfPrefix 4).getD k 0) (fun k => (egfPrefix 4).getD k 0)) (compSeq (fun k => (egfPrefix 4).getD k 0) (fun k => (egfPrefix 4).getD k 0))) 4] = _
  rw [hprev]
  change [0, 1, 1, 9 / 2, 205 / 6] ++ [expSeq p4 4] = _
  rw [hexp]
  rfl

private lemma a396804_5 : a396804 5 = (41005 : ℚ) := by
  unfold a396804
  rw [egfPrefix_5]
  norm_num [Nat.factorial]

private lemma disprove_main :
    ¬ (∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, a396804 n = (m : ℚ) ∧ m % 3 = n % 3) := by
  intro h
  obtain ⟨m, hm, hmod⟩ := h 5 (by decide)
  rw [a396804_5] at hm
  have hm_eq : m = 41005 := by exact_mod_cast hm.symm
  rw [hm_eq] at hmod
  omega

end OMA.P_oeis_a396804

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a396804.main) :=
  OMA.P_oeis_a396804.disprove_main
