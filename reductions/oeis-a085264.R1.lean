import OMAStatements.S_oeis_a085264
import Mathlib

/-!
# Effective bounds, the finite tables, and nonempty levels for A085264

Source: https://oeis.org/A085264
Credit: @dwilfand-sys

Robert G. Wilson v conjectured the greatest-element and frequency statements
for the positive-square representation count of Reinhard Zumkeller's A085263.
The asymptotic in Section 4 of Jorge Jiménez Urroz, Expositiones Mathematicae
40 (2022), implies finiteness of individual levels. Our elementary sieve
gives the explicit polynomial in H1. H2 and H3 use the cutoff 3202 squared
from our independent interval estimate and finite computations. Every listed
frequency is positive, so H4 asks for witnesses only at unlisted levels.
-/

namespace OMA.R_oeis_a085264_R1

open OMA.S_oeis_a085264

def H1 : Prop := ∀ k n : ℕ, 0 < n → representations n ≤ k →
    n ≤ (2 * (100 * (k + 300000) + 15 * k ^ 2) + 2) ^ 2

def H2 : Prop := ∀ n : ℕ, 10252804 < n → 100 < representations n

def H3 : Prop :=
  let T : ℕ → Finset ℕ := fun j =>
    (Finset.Icc 1 10252804).filter (fun n => representations n = j)
  T 0 = {1,13} ∧
    (∀ i : Fin lastTable.length, IsGreatest (T i.val : Set ℕ) (lastTable.get i)) ∧
    (∀ i : Fin frequencyTable.length, (T i.val).card = frequencyTable.get i)

def H4 : Prop := ∀ j : ℕ, frequencyTable.length ≤ j → (level j).Nonempty

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a085264.main := by
  intro hbound htail hdata hwitness
  let T : ℕ → Finset ℕ := fun j =>
    (Finset.Icc 1 10252804).filter (fun n => representations n = j)
  change T 0 = {1,13} ∧
    (∀ i : Fin lastTable.length, IsGreatest (T i.val : Set ℕ) (lastTable.get i)) ∧
    (∀ i : Fin frequencyTable.length, (T i.val).card = frequencyTable.get i) at hdata
  obtain ⟨hzero, hlast, hcount⟩ := hdata
  have hfinite (j : ℕ) : (level j).Finite := by
    apply (Set.finite_Iic ((2 * (100 * (j + 300000) + 15 * j ^ 2) + 2) ^ 2)).subset
    intro n hn
    obtain ⟨hp, he⟩ := hn
    exact hbound j n hp he.le
  have clipped (j : ℕ) (hj : j ≤ 100) : level j = (T j : Set ℕ) := by
    ext n
    change (0 < n ∧ representations n = j) ↔ n ∈ T j
    simp only [T, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hp, he⟩
      have hcap : n ≤ 10252804 := by
        by_contra! hn
        have hmore := htail n hn
        omega
      exact ⟨⟨by omega, hcap⟩, he⟩
    · rintro ⟨⟨hl, _⟩, he⟩
      exact ⟨by omega, he⟩
  have nlast : lastTable.length = 81 := by decide
  have nfreq : frequencyTable.length = 101 := by decide
  have frequencies (i : Fin frequencyTable.length) : (level i.val).ncard = frequencyTable.get i := by
    have hi := i.isLt
    calc
      _ = (T i.val : Set ℕ).ncard := congrArg Set.ncard (clipped i.val (by omega))
      _ = (T i.val).card := Set.ncard_coe_finset _
      _ = _ := hcount i
  have positive : ∀ i : Fin frequencyTable.length, 0 < frequencyTable.get i := by decide +kernel
  refine ⟨?_, hfinite, ?_, ?_, frequencies⟩
  · intro j
    apply (hfinite j).bddAbove.exists_isGreatest_of_nonempty
    by_cases hj : j < frequencyTable.length
    · apply (Set.ncard_pos (hfinite j)).mp
      calc
        0 < frequencyTable.get ⟨j,hj⟩ := positive _
        _ = (level j).ncard := (frequencies ⟨j,hj⟩).symm
    · exact hwitness j (by omega)
  · simpa only [hzero, Finset.coe_insert, Finset.coe_singleton] using clipped 0 (by decide)
  · intro i
    have hi := i.isLt
    rw [clipped i.val (by omega)]
    exact hlast i

end OMA.R_oeis_a085264_R1
