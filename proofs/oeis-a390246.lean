import OMAStatements.S_oeis_a390246
import Mathlib.Tactic

open OMA.S_oeis_a390246

namespace MatchingIntervals

lemma endpoints_nonempty (n : ℕ) : (endpoints n).Nonempty := by
  refine ⟨(n + 1) * n, fun i => (n + 1) * (i.val + 1), ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    have h' : i.val + 1 = j.val + 1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n + 1) h
    omega
  · intro i
    refine ⟨dvd_mul_left _ _, ?_, Nat.mul_le_mul_left _ i.isLt⟩
    have h := Nat.mul_le_mul_left (n + 1) (show 1 ≤ i.val + 1 by omega)
    simpa using h

lemma to_width {n u : ℕ} (hn : 1 ≤ n) (h : u ∈ endpoints n) :
    u - (n - 1) ∈ widths n := by
  obtain ⟨b, injective, hb⟩ := h
  refine ⟨b, injective, fun i => ?_⟩
  obtain ⟨hd, hlo, hhi⟩ := hb i
  exact ⟨hd, by omega, by omega⟩

lemma to_endpoint {n k : ℕ} (h : k ∈ widths n) : n + k - 1 ∈ endpoints n := by
  obtain ⟨b, injective, hb⟩ := h
  refine ⟨b, injective, fun i => ?_⟩
  obtain ⟨hd, hlo, hhi⟩ := hb i
  exact ⟨hd, by omega, by omega⟩

end MatchingIntervals

open MatchingIntervals

theorem OMA.solution : type_of% @OMA.S_oeis_a390246.main := by
  intro n hn
  have he := Nat.sInf_mem (endpoints_nonempty n)
  have hw := to_width hn he
  have hwmin := Nat.sInf_mem (show (widths n).Nonempty from ⟨_, hw⟩)
  have hupper := Nat.sInf_le (to_endpoint hwmin)
  exact Nat.le_antisymm (Nat.sInf_le hw) (by omega)
