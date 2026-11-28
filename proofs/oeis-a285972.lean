import OMAStatements.S_oeis_a285972
import Mathlib

/-!
# A285972: the {10->1}-transform of Thue-Morse is 0 followed by the {01->1}-transform

rep10 deletes each 0 that comes right after a 1 and rep01 deletes each 0 that comes right before a
1. For every word u over {0, 1}, rep10(u) is an initial segment of rep01(0 u): by induction on u,
following the cases 0 u', 1, 1 0 r and 1 1 r. The first 2n+2 letters of the Thue-Morse word are
0 u for such a word u, rep10(0 u) = 0 rep10(u), and rep10(u) has at least n letters. So letter n of
rep10(0 u) is letter n - 1 of rep10(u), which is letter n - 1 of rep01(0 u).
-/

namespace OMA.P285972

open OMA.S_oeis_a285972

theorem key : ∀ u : List ℕ, (∀ x ∈ u, x ≤ 1) → ∃ s, rep01 (0 :: u) = rep10 u ++ s
  | [], _ => ⟨[0], by simp [rep01, rep10]⟩
  | 0 :: u, h => by
    obtain ⟨s, hs⟩ := key u (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨s, ?_⟩
    have e1 : rep01 (0 :: 0 :: u) = 0 :: rep01 (0 :: u) := by simp [rep01]
    have e2 : rep10 (0 :: u) = 0 :: rep10 u := by simp [rep10]
    rw [e1, e2, hs]
    rfl
  | [1], _ => ⟨[], by simp [rep01, rep10]⟩
  | 1 :: 0 :: r, h => by
    obtain ⟨s, hs⟩ := key r (fun x hx => h x (by simp [hx]))
    refine ⟨s, ?_⟩
    have e1 : rep01 (0 :: 1 :: 0 :: r) = 1 :: rep01 (0 :: r) := by simp [rep01]
    have e2 : rep10 (1 :: 0 :: r) = 1 :: rep10 r := by simp [rep10]
    rw [e1, e2, hs]
    rfl
  | 1 :: 1 :: r, h => by
    obtain ⟨s, hs⟩ := key (1 :: r) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨s, ?_⟩
    have e1 : rep01 (0 :: 1 :: 1 :: r) = 1 :: rep01 (1 :: r) := by simp [rep01]
    have e2 : rep10 (1 :: 1 :: r) = 1 :: rep10 (1 :: r) := by simp [rep10]
    have e3 : rep01 (1 :: r) = rep01 (0 :: 1 :: r) := by simp [rep01]
    rw [e1, e2, e3, hs]
    rfl
  | 1 :: (c + 2) :: r, h => by
    have := h (c + 2) (by simp)
    omega
  | (c + 2) :: u, h => by
    have := h (c + 2) (by simp)
    omega

theorem len10 : ∀ w : List ℕ, w.length ≤ 2 * (rep10 w).length
  | [] => by simp [rep10]
  | 1 :: 0 :: w => by
    have := len10 w
    have e : rep10 (1 :: 0 :: w) = 1 :: rep10 w := by simp [rep10]
    rw [e]
    simp
    omega
  | 0 :: w => by
    have := len10 w
    have e : rep10 (0 :: w) = 0 :: rep10 w := by simp [rep10]
    rw [e]
    simp
    omega
  | [1] => by simp [rep10]
  | 1 :: (c + 1) :: w => by
    have := len10 ((c + 1) :: w)
    have e : rep10 (1 :: (c + 1) :: w) = 1 :: rep10 ((c + 1) :: w) := by simp [rep10]
    rw [e]
    simp only [List.length_cons] at this ⊢
    omega
  | (c + 2) :: w => by
    have := len10 w
    have e : rep10 ((c + 2) :: w) = (c + 2) :: rep10 w := by simp [rep10]
    rw [e]
    simp
    omega

lemma tmWord_succ (L : ℕ) : tmWord (L + 1) = 0 :: (List.range L).map (fun i => tm (i + 1)) := by
  unfold tmWord
  rw [List.range_succ_eq_map]
  simp [tm, Function.comp_def]

lemma tm_le (i : ℕ) : tm i ≤ 1 := by
  unfold tm
  omega

theorem sol : type_of% @OMA.S_oeis_a285972.main := by
  intro n hn
  unfold a A285960
  have hL : 2 * (n - 1) + 4 = 2 * n + 1 + 1 := by omega
  rw [hL, tmWord_succ]
  set u := (List.range (2 * n + 1)).map (fun i => tm (i + 1)) with hu
  have hub : ∀ x ∈ u, x ≤ 1 := by
    intro x hx
    rw [hu, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact tm_le _
  obtain ⟨s, hs⟩ := key u hub
  have e : rep10 (0 :: u) = 0 :: rep10 u := by simp [rep10]
  rw [e, hs]
  have hlen := len10 u
  have hul : u.length = 2 * n + 1 := by simp [hu]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [List.getD_eq_getElem?_getD]
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 1 - 1 = m := by omega
  rw [h1, h2, List.getElem?_cons_succ, List.getElem?_append_left (by omega)]

end OMA.P285972

theorem OMA.solution : type_of% @OMA.S_oeis_a285972.main := OMA.P285972.sol

