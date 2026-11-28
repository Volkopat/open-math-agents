import OMAStatements.S_oeis_a386703
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries

/-!
# Pentagonal support of strict partition parity and centered residues

Source: https://oeis.org/A386703
-/

open OMA.S_oeis_a386703

namespace OMA.R_oeis_a386703_R1

open PowerSeries PowerSeries.WithPiTopology

/-- Over `ZMod 2`, the generating function for strict partitions is the
pentagonal series. -/
theorem strict_partition_series_mod_two :
    PowerSeries.mk (fun n => (q n : ZMod 2)) = pentagonalSeries (ZMod 2) := by
  let : TopologicalSpace (ZMod 2) := ⊥
  let : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  have hp := Nat.Partition.hasProd_powerSeriesMk_card_countRestricted (ZMod 2) (m := 2)
    (by decide)
  simp_rw [Nat.Partition.countRestricted_two] at hp
  have hfactor (i : ℕ) : (∑ j ∈ Finset.range 2, (X : (ZMod 2)⟦X⟧) ^ ((i + 1) * j)) =
      (1 : (ZMod 2)⟦X⟧) - X ^ (i + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [mul_zero, pow_zero, mul_one]
    ext n
    simp only [map_add, map_sub]
    exact (CharTwo.sub_eq_add _ _).symm
  simp_rw [hfactor] at hp
  exact hp.unique (hasProd_one_sub_X_pow (ZMod 2))

/-- Away from generalized pentagonal numbers, the number of strict partitions
is even, and at every generalized pentagonal number it is odd. -/
theorem even_q_iff_nonpentagonal (n : ℕ) : Even (q n) ↔ n ∉ Set.range pentagonal := by
  have hcoeff := congrArg (fun P : (ZMod 2)⟦X⟧ => P.coeff n) strict_partition_series_mod_two
  rw [PowerSeries.coeff_mk] at hcoeff
  rw [even_iff_two_dvd, ← ZMod.natCast_eq_zero_iff, hcoeff,
    PowerSeries.coeff_pentagonalSeries_eq_zero_iff]

private theorem pentagonal_discriminant (k : ℤ) :
    24 * (pentagonal k : ℤ) + 1 = (6 * k - 1) ^ 2 := by
  nlinarith only [two_mul_natCast_pentagonal k]

/-- The generalized pentagonal indices are exactly those detected by the
square test `24 * n + 1`. -/
theorem pentagonal_iff_square (n : ℕ) : n ∈ Set.range pentagonal ↔ IsSquare (24 * n + 1) := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨(6 * k - 1).natAbs, ?_⟩
    have heq : ((24 * pentagonal k + 1 : ℕ) : ℤ) = (6 * k - 1) ^ 2 := by
      push_cast
      exact pentagonal_discriminant k
    have h := congrArg Int.natAbs heq
    simpa only [Int.natAbs_natCast, pow_two, Int.natAbs_mul] using h
  · rintro ⟨s, hs⟩
    have hsq : (24 : ℤ) * (n : ℤ) + 1 = (s : ℤ) ^ 2 := by
      rw [pow_two]
      exact_mod_cast hs
    have hmod : s * s % 6 = 1 := by rw [← hs]; omega
    have hres : s % 6 = 1 ∨ s % 6 = 5 := by
      rw [Nat.mul_mod] at hmod
      have hcases : ∀ t : Fin 6, t.val * t.val % 6 = 1 → t.val = 1 ∨ t.val = 5 := by decide
      exact hcases ⟨s % 6, Nat.mod_lt s (by decide)⟩ hmod
    rcases hres with h1 | h5
    · let k : ℤ := -((s : ℤ) / 6)
      refine ⟨k, ?_⟩
      have hk : 6 * k - 1 = -(s : ℤ) := by dsimp [k]; omega
      have heq : 24 * (pentagonal k : ℤ) + 1 = (s : ℤ) ^ 2 := by
        rw [pentagonal_discriminant, hk]
        ring
      exact_mod_cast (show (pentagonal k : ℤ) = (n : ℤ) by omega)
    · let k : ℤ := (s : ℤ) / 6 + 1
      refine ⟨k, ?_⟩
      have hk : 6 * k - 1 = (s : ℤ) := by dsimp [k]; omega
      have heq : 24 * (pentagonal k : ℤ) + 1 = (s : ℤ) ^ 2 := by
        rw [pentagonal_discriminant, hk]
      exact_mod_cast (show (pentagonal k : ℤ) = (n : ℤ) by omega)

/-- An integer-square test for the parity of the strict partition function. -/
theorem even_q_iff_nonsquare (n : ℕ) : Even (q n) ↔ ¬ IsSquare (24 * n + 1) := by
  rw [even_q_iff_nonpentagonal, pentagonal_iff_square]

/-- When the index is nonpentagonal, centered residues have the parity of the
ordinary partition count. -/
theorem centered_residue_mod_two {n : ℕ} {r : ℤ} (hn : ¬ IsSquare (24 * n + 1))
    (hr : IsCenteredResidue n r) : r ≡ (p n : ℤ) [ZMOD 2] := by
  have hq : (2 : ℤ) ∣ (q n : ℤ) := by
    exact_mod_cast even_iff_two_dvd.mp ((even_q_iff_nonsquare n).mpr hn)
  exact Int.modEq_iff_dvd.mpr (hq.trans hr.1.dvd)

/-- For nonpentagonal indices, a counterexample has zero centered residue
when the ordinary partition count is even, and unit residue when it is odd. -/
theorem nonpentagonal_small_residue_cases {n : ℕ} {r : ℤ}
    (hn : ¬ IsSquare (24 * n + 1)) (hr : IsCenteredResidue n r) (hsmall : |r| ≤ 1) :
    (Even (p n) ∧ r = 0) ∨ (Odd (p n) ∧ (r = -1 ∨ r = 1)) := by
  have hmod := centered_residue_mod_two hn hr
  rw [Int.ModEq] at hmod
  have hbound := abs_le.mp hsmall
  have hcases : r = -1 ∨ r = 0 ∨ r = 1 := by omega
  have hpEven : Even (p n) ↔ (p n : ℤ) % 2 = 0 := by
    rw [even_iff_two_dvd, ← Int.natCast_dvd_natCast, Int.dvd_iff_emod_eq_zero]
    norm_num
  have hpOdd : Odd (p n) ↔ (p n : ℤ) % 2 = 1 := by
    rw [Nat.odd_iff]
    omega
  rcases hcases with h | h | h
  · exact Or.inr ⟨hpOdd.mpr (by omega), Or.inl h⟩
  · exact Or.inl ⟨hpEven.mpr (by omega), h⟩
  · exact Or.inr ⟨hpOdd.mpr (by omega), Or.inr h⟩

/-- At generalized pentagonal indices, the strict partition count is odd. -/
def H1 : Prop :=
  ∀ n : ℕ, 7 < n → IsSquare (24 * n + 1) →
    ∀ r : ℤ, IsCenteredResidue n r → 1 < |r|

/-- At other indices with an even partition count, only zero can violate the bound. -/
def H2 : Prop :=
  ∀ n : ℕ, 7 < n → ¬ IsSquare (24 * n + 1) → Even (p n) →
    ¬ (q n : ℤ) ∣ (p n : ℤ)

/-- At other indices with an odd partition count, exclude the residue one. -/
def H3 : Prop :=
  ∀ n : ℕ, 7 < n → ¬ IsSquare (24 * n + 1) → Odd (p n) →
    ¬ (q n : ℤ) ∣ (p n : ℤ) - 1

/-- At other indices with an odd partition count, exclude the residue minus one. -/
def H4 : Prop :=
  ∀ n : ℕ, 7 < n → ¬ IsSquare (24 * n + 1) → Odd (p n) →
    ¬ (q n : ℤ) ∣ (p n : ℤ) + 1

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a386703.main := by
  intro hpent hzero hpos hneg n hn r hr
  by_cases hsq : IsSquare (24 * n + 1)
  · exact hpent n hn hsq r hr
  · by_contra! hsmall
    rcases nonpentagonal_small_residue_cases hsq hr hsmall with ⟨he, rfl⟩ | ⟨ho, h | h⟩
    · exact hzero n hn hsq he (by simpa using hr.1.dvd)
    · subst r
      exact hneg n hn hsq ho (by simpa using hr.1.dvd)
    · subst r
      exact hpos n hn hsq ho hr.1.dvd

end OMA.R_oeis_a386703_R1
