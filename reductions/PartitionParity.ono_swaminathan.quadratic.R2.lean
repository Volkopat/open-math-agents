import FormalConjectures.Paper.PartitionParity
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Basic

/-!
An alternative reduction using the mod-2 Lambert expansion in
Ono and Swaminathan. Nonperiodicity of the two transformed coefficient sequences
implies that both parities occur infinitely often. Finite support
of either parity would give an explicit factorial period.

Source: https://arxiv.org/abs/2509.09553v4, Sections 2.4 and 4.
Credit: @justusklocke-cloud
-/

open Finset Nat
open scoped BigOperators

namespace OMA.R_PartitionParity_ono_swaminathan_quadratic_R2

private theorem finite_lambert_period (D M : ℕ) (a : ℕ → ZMod 2)
    (ha : ∀ m > M, m.Coprime 6 → a m = 0) (n : ℕ) (hn : 0 < n) :
    (∑ m ∈ (n + D * M.factorial).divisors,
      if m.Coprime 6 ∧ ((n + D * M.factorial) / m).Coprime D then a m else 0) =
    (∑ m ∈ n.divisors, if m.Coprime 6 ∧ (n / m).Coprime D then a m else 0) := by
  let P := D * M.factorial
  let summand (N m : ℕ) := if m.Coprime 6 ∧ (N / m).Coprime D then a m else 0
  change (∑ m ∈ (n + P).divisors, summand (n + P) m) = ∑ m ∈ n.divisors, summand n m
  have truncation (N : ℕ) :
      (∑ m ∈ N.divisors.filter (fun m => m ≤ M), summand N m) =
        ∑ m ∈ N.divisors, summand N m := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro m hm hnot
    have hlarge : M < m := Nat.lt_of_not_ge fun h => hnot (Finset.mem_filter.mpr ⟨hm, h⟩)
    unfold summand
    split_ifs with h
    · exact ha m hlarge h.1
    · rfl
  have hperiod (m : ℕ) (hm : 0 < m) (hle : m ≤ M) : ∃ k : ℕ, P = m * (D * k) := by
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hm hle
    exact ⟨k, by simp [P, hk, Nat.mul_left_comm]⟩
  have hsets : (n + P).divisors.filter (fun m => m ≤ M) =
      n.divisors.filter (fun m => m ≤ M) := by
    ext m
    have hshift : 0 < n + P := Nat.lt_of_lt_of_le hn (Nat.le_add_right n P)
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hm, hle⟩
      obtain ⟨k, hk⟩ := hperiod m (Nat.pos_of_mem_divisors hm) hle
      have hdvd : m ∣ P := ⟨D * k, hk⟩
      exact ⟨Nat.mem_divisors.mpr ⟨(Nat.dvd_add_iff_left hdvd).mpr
        (Nat.dvd_of_mem_divisors hm), hn.ne'⟩, hle⟩
    · rintro ⟨hm, hle⟩
      obtain ⟨k, hk⟩ := hperiod m (Nat.pos_of_mem_divisors hm) hle
      have hdvd : m ∣ P := ⟨D * k, hk⟩
      exact ⟨Nat.mem_divisors.mpr ⟨(Nat.dvd_add_iff_left hdvd).mp
        (Nat.dvd_of_mem_divisors hm), hshift.ne'⟩, hle⟩
  rw [← truncation (n + P), ← truncation n, hsets]
  refine Finset.sum_congr rfl ?_
  intro m hm
  obtain ⟨hm, hle⟩ := Finset.mem_filter.mp hm
  have hpos := Nat.pos_of_mem_divisors hm
  obtain ⟨k, hk⟩ := hperiod m hpos hle
  simp only [summand, hk, Nat.add_mul_div_left n (D * k) hpos, Nat.coprime_add_mul_left_left]

/-- Nonperiodicity of the transform of the parity. -/
def H1 : Prop := ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
  ∀ P : ℕ, 0 < P → ∃ n : ℕ, 0 < n ∧
    (∑ m ∈ (n + P).divisors,
      if m.Coprime 6 ∧ ((n + P) / m).Coprime D then
        (partitionNumber ((D * m ^ 2 + 1) / 24) : ZMod 2)
      else 0) ≠
    (∑ m ∈ n.divisors,
      if m.Coprime 6 ∧ (n / m).Coprime D then
        (partitionNumber ((D * m ^ 2 + 1) / 24) : ZMod 2)
      else 0)

/-- Nonperiodicity of the transform of one minus the parity. -/
def H2 : Prop := ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
  ∀ P : ℕ, 0 < P → ∃ n : ℕ, 0 < n ∧
    (∑ m ∈ (n + P).divisors,
      if m.Coprime 6 ∧ ((n + P) / m).Coprime D then
        1 - (partitionNumber ((D * m ^ 2 + 1) / 24) : ZMod 2)
      else 0) ≠
    (∑ m ∈ n.divisors,
      if m.Coprime 6 ∧ (n / m).Coprime D then
        1 - (partitionNumber ((D * m ^ 2 + 1) / 24) : ZMod 2)
      else 0)

theorem main : H1 → H2 → type_of% @PartitionParity.ono_swaminathan.quadratic := by
  intro oddNonperiodic evenNonperiodic D hD hsq hDmod
  constructor
  · apply Set.infinite_of_not_bddAbove
    rintro ⟨M, hM⟩
    let a (m : ℕ) : ZMod 2 := 1 - (partitionNumber ((D * m ^ 2 + 1) / 24) : ZMod 2)
    have hsupport : ∀ m > M, m.Coprime 6 → a m = 0 := by
      intro m hmt hm
      have hne : ¬ Even (partitionNumber ((D * m ^ 2 + 1) / 24)) := by
        intro he
        exact (not_le_of_gt hmt) (hM ⟨hm, he⟩)
      have hodd := Nat.not_even_iff_odd.mp hne
      rw [show a m = 1 - (partitionNumber ((D * m ^ 2 + 1) / 24) : ZMod 2) by rfl,
        hodd.natCast_zmod_two, sub_self]
    obtain ⟨n, hn, hneq⟩ := evenNonperiodic D hD hsq hDmod (D * M.factorial) (by positivity)
    exact hneq (finite_lambert_period D M a hsupport n hn)
  · apply Set.infinite_of_not_bddAbove
    rintro ⟨M, hM⟩
    let a (m : ℕ) : ZMod 2 := (partitionNumber ((D * m ^ 2 + 1) / 24) : ZMod 2)
    have hsupport : ∀ m > M, m.Coprime 6 → a m = 0 := by
      intro m hmt hm
      have hne : ¬ Odd (partitionNumber ((D * m ^ 2 + 1) / 24)) := by
        intro ho
        exact (not_le_of_gt hmt) (hM ⟨hm, ho⟩)
      exact (Nat.not_odd_iff_even.mp hne).natCast_zmod_two
    obtain ⟨n, hn, hneq⟩ := oddNonperiodic D hD hsq hDmod (D * M.factorial) (by positivity)
    exact hneq (finite_lambert_period D M a hsupport n hn)

end OMA.R_PartitionParity_ono_swaminathan_quadratic_R2
