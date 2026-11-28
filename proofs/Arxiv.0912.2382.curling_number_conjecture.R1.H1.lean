import OMAReductions.R_Arxiv_0912_2382_curling_number_conjecture_R1
import Mathlib

open Arxiv.«0912.2382»

private theorem curling_append_fresh (L : List ℤ) (c : ℤ) (hc : c ∉ L) :
    k (L ++ [c]) = 1 := by
  have hn : L ++ [c] ≠ [] := by simp
  have hp := one_le_k hn
  by_contra h
  obtain ⟨X, Y, hY, hrep⟩ := k_attained hn
  obtain ⟨r, hr⟩ : ∃ r : ℕ, k (L ++ [c]) = (r + 1) + 1 := ⟨k (L ++ [c]) - 2, by omega⟩
  have hs (n : ℕ) :
      (List.replicate (n + 1) Y).flatten = (List.replicate n Y).flatten ++ Y := by
    rw [List.replicate_succ', List.flatten_append]
    simp
  rw [hr, hs, hs] at hrep
  obtain ⟨Z, y, rfl⟩ : ∃ (Z : List ℤ) (y : ℤ), Y = Z ++ [y] := by
    induction Y using List.reverseRecOn with
    | nil => exact (hY rfl).elim
    | append_singleton Z y ih => exact ⟨Z, y, rfl⟩
  let W := X ++ (List.replicate r (Z ++ [y])).flatten
  have he : L ++ [c] = (W ++ (Z ++ [y]) ++ Z) ++ [y] := by
    simpa only [W, List.append_assoc] using hrep
  have hcy : c = y := by
    have hh := congrArg List.reverse he
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.cons.injEq] at hh
    exact hh.1
  subst c
  have hL := List.append_cancel_right he
  apply hc
  rw [hL]
  simp

theorem OMA.solution : OMA.R_Arxiv_0912_2382_curling_number_conjecture_R1.H1 := by
  rintro L _ ⟨m, hm⟩
  exact ⟨m + 1, curling_append_fresh (S L m) (k (S L m)) hm⟩