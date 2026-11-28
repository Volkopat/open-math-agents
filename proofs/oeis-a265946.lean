import OMAStatements.S_oeis_a265946
import Mathlib

open OMA.S_oeis_a265946


theorem OMA.solution : type_of% @OMA.S_oeis_a265946.main := by
  intro n hn hreach
  have hstop : collatz^[stop n] n = 1 := Nat.sInf_mem hreach
  have h1 : a (2 * n) = -∑ i ∈ Finset.range (stop n), min (diff n i) 0 := by
    unfold a
    rw [if_neg (by omega), show 2 * n / 2 = n by omega]
  have h2 : a (2 * n - 1) = ∑ i ∈ Finset.range (stop n), max (diff n i) 0 := by
    unfold a
    rw [if_pos (by omega), show (2 * n - 1 + 1) / 2 = n by omega]
  rw [h1, h2]
  have tele : ∑ i ∈ Finset.range (stop n), diff n i = (1 : ℤ) - n := by
    unfold diff
    rw [Finset.sum_range_sub (fun i => ((collatz^[i] n : ℕ) : ℤ)), hstop]
    simp
  have split : ∀ i, max (diff n i) 0 + min (diff n i) 0 = diff n i := by
    intro i
    rcases le_total (diff n i) 0 with h | h
    · rw [max_eq_right h, min_eq_left h]; ring
    · rw [max_eq_left h, min_eq_right h]; ring
  have hs : ∑ i ∈ Finset.range (stop n), max (diff n i) 0 + ∑ i ∈ Finset.range (stop n), min (diff n i) 0 =
      (1 : ℤ) - n := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun i _ => split i), tele]
  linarith
