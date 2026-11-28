import OMAStatements.S_oeis_a321612
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open OMA.S_oeis_a321612

namespace TriangularComplements

private lemma succ_tri (r : ℕ) : tri (r+1) = tri r + (r+1) := by
  simpa [tri, Nat.mul_comm] using Nat.triangle_succ (r+1)

private lemma increasing : StrictMono tri :=
  strictMono_nat_of_lt_succ fun i => by rw [succ_tri]; omega

private lemma index_le (i : ℕ) : i ≤ tri i := by
  induction i with
  | zero => decide
  | succ i ih => rw [succ_tri]; omega

private lemma is_tri (i : ℕ) : triangular (tri i) :=
  ⟨⟨i, Nat.lt_succ_of_le (index_le i)⟩, rfl⟩

private lemma central_bound {u : ℕ} (hu : 5 ≤ u) : 2*u+5 ≤ tri (u+1) := by
  induction u, hu using Nat.le_induction with
  | base => decide
  | succ u hu ih => rw [succ_tri (u+1)]; omega

/-- Just below the midpoint, adjacent triangular numbers have too small
a gap, while skipping even one index gives too large a gap. -/
private lemma no_gap {u b c : ℕ} (hu : 5 ≤ u) (hb : u ≤ b) (hb' : b ≤ u+2) :
    tri b ≠ tri c + (u+3) := by
  intro h
  have hc : c < b := increasing.lt_iff_lt.mp (by omega)
  by_cases ha : b = c+1
  · rw [ha, succ_tri] at h
    omega
  · let v := b-2
    have hv : b = v+2 := by dsimp [v]; omega
    have hcv : c ≤ v := by omega
    have hle := increasing.monotone hcv
    rw [hv, succ_tri (v+1), succ_tri v] at h
    omega

private lemma bound {k : ℕ} (h : inTerms k) : k ≤ 42 := by
  by_contra! hk
  have ex : ∃ s : ℕ, k ≤ 2*tri s := ⟨k, by have := index_le k; omega⟩
  let s := Nat.find ex
  have hs : k ≤ 2*tri s := Nat.find_spec ex
  have hs7 : 7 ≤ s := by
    by_contra! hsmall
    have hle : tri s ≤ tri 6 := increasing.monotone (by omega)
    have h6 : tri 6 = 21 := by decide
    omega
  let u := s-2
  have hu : 5 ≤ u := by dsimp [u]; omega
  have hsu : s = u+2 := by dsimp [u]; omega
  have hprev : 2*tri (u+1) < k :=
    Nat.lt_of_not_ge (Nat.find_min ex (show u+1 < s by omega))
  have hh : k ≤ 2*tri (u+2) := hsu ▸ hs
  have hc := central_bound hu
  have h1 : tri (u+1) = tri u + (u+1) := succ_tri u
  have h2 : tri (u+2) = tri (u+1) + (u+2) := succ_tri (u+1)
  have h3 : tri (u+3) = tri (u+2) + (u+3) := succ_tri (u+2)
  have ht : tri (u+2) < k := by omega
  have ht' : tri (u+3) < k := by omega
  obtain ⟨⟨b, _⟩, hb⟩ := h.2 ⟨tri (u+2), ht⟩ hh (is_tri _)
  obtain ⟨⟨c, _⟩, hd⟩ := h.2 ⟨tri (u+3), ht'⟩ (by dsimp; omega) (is_tri _)
  change tri b = k - tri (u+2) at hb
  change tri c = k - tri (u+3) at hd
  have hub : u ≤ b := increasing.le_iff_le.mp (by omega)
  have hbu : b ≤ u+2 := increasing.le_iff_le.mp (by omega)
  exact no_gap hu hub hbu (c := c) (by omega)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1800000 in
private lemma checked : ∀ k : Fin 43,
    inTerms k ↔ k.val ∈ ({2, 4, 6, 7, 9, 13, 16, 21, 31} : Set ℕ) := by
  simp only [inTerms, triangular, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide

end TriangularComplements

theorem OMA.solution : type_of% @OMA.S_oeis_a321612.main := by
  ext k
  change inTerms k ↔ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 9 ∨ k = 13 ∨ k = 16 ∨ k = 21 ∨ k = 31
  by_cases h : k < 43
  · exact TriangularComplements.checked ⟨k, h⟩
  · have hn : ¬inTerms k := fun ht => by have := TriangularComplements.bound ht; omega
    constructor
    · exact fun hmem => (hn hmem).elim
    · intro hmem
      exfalso
      omega
