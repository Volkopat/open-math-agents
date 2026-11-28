import OMAReductions.R_Erdos423_erdos_423_variants_upper_bound_R1
import Mathlib

/-! Reduction from block sums to differences of a strictly convex sequence. -/

-- Even-indexed prefix sums turn positive differences into block sums
-- of length at least two, without any loss from singleton sums.
-- Credit: @Cristian-Andrei-Pomenea

open Finset BigOperators Filter

namespace OMA.R_Erdos423_erdos_423_variants_upper_bound_R1_H1_R1

theorem prefix_diff (a : ℕ → ℕ) {i j : ℕ} (hij : i < j) :
    (∑ t ∈ range (2 * j + 1), a t) -
      (∑ t ∈ range (2 * i + 1), a t) =
        ∑ t ∈ Icc (2 * i + 1) (2 * j), a t := by
  have hs := Finset.sum_range_add_sum_Ico a
    (show 2 * i + 1 ≤ 2 * j + 1 by omega)
  have heq :
      Ico (2 * i + 1) (2 * j + 1) =
        Icc (2 * i + 1) (2 * j) := by
    ext x
    simp only [mem_Ico, mem_Icc]
    omega
  rw [← heq]
  omega

-- Convex difference-set expansion, in the positive-difference formulation.
def H1 : Prop :=
  ∀ p : ℕ → ℕ,
    StrictMono p →
    StrictMono (fun k => p (k + 1) - p k) →
    ∀ η : ℝ, 0 < η →
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ k : ℕ in atTop,
        (k : ℝ) ^ ((1101 : ℝ) / 688 - η) ≤
          C * (({s : ℕ | ∃ i j : ℕ,
            i < j ∧ j ≤ k ∧ s = p j - p i}).ncard : ℝ)

-- Eventual power bounds transfer from half-indices with a constant loss.
def H2 : Prop :=
  ∀ b d : ℕ → ℕ,
    (∀ m, b (m / 2) ≤ d m) →
    ∀ r : ℝ,
      (∃ C : ℝ, 0 < C ∧
        ∀ᶠ k : ℕ in atTop,
          (k : ℝ) ^ r ≤ C * (b k : ℝ)) →
      ∃ D : ℝ, 0 < D ∧
        ∀ᶠ m : ℕ in atTop,
          (m : ℝ) ^ r ≤ D * (d m : ℝ)

theorem main : H1 → H2 →
    OMA.R_Erdos423_erdos_423_variants_upper_bound_R1.H1 := by
  intro hconv hscale a ha η hη
  let p : ℕ → ℕ := fun k => ∑ t ∈ range (2 * k + 1), a t
  have hgap (k : ℕ) :
      p (k + 1) - p k =
        a (2 * k + 1) + a (2 * k + 2) := by
    change
      (∑ t ∈ range (2 * (k + 1) + 1), a t) -
        (∑ t ∈ range (2 * k + 1), a t) = _
    rw [prefix_diff a (Nat.lt_succ_self k)]
    have heq :
        Icc (2 * k + 1) (2 * (k + 1)) =
          {2 * k + 1, 2 * k + 2} := by
      ext x
      simp only [mem_Icc, mem_insert, mem_singleton]
      omega
    rw [heq, sum_pair (by omega)]
  have hp : StrictMono p := by
    apply strictMono_nat_of_lt_succ
    intro k
    have hpos : a 1 < a (2 * k + 2) :=
      ha (show 0 < 2 * k + 1 by omega)
    have h := hgap k
    omega
  have hc : StrictMono
      (fun k => p (k + 1) - p k) := by
    apply strictMono_nat_of_lt_succ
    intro k
    change p (k + 1) - p k <
      p (k + 1 + 1) - p (k + 1)
    rw [hgap k, hgap (k + 1)]
    have h1 :
        a (2 * k + 1) < a (2 * (k + 1) + 1) :=
      ha (show 2 * k < 2 * (k + 1) by omega)
    have h2 :
        a (2 * k + 2) < a (2 * (k + 1) + 2) :=
      ha (show 2 * k + 1 < 2 * (k + 1) + 1 by omega)
    omega
  let b : ℕ → ℕ := fun k =>
    ({s : ℕ | ∃ i j : ℕ,
      i < j ∧ j ≤ k ∧ s = p j - p i}).ncard
  let d : ℕ → ℕ := fun m =>
    ({s : ℕ |
      Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard
  have hsub (m : ℕ) : b (m / 2) ≤ d m := by
    have hs :
        {s : ℕ | ∃ i j : ℕ,
          i < j ∧ j ≤ m / 2 ∧ s = p j - p i} ⊆
        {s : ℕ |
          Erdos423.IsConsecutiveBlockSum a (m + 1) s} := by
      rintro s ⟨i, j, hij, hj, rfl⟩
      exact ⟨2 * i + 1, 2 * j,
        by omega, by omega, by omega,
        prefix_diff a hij⟩
    have hf :
        ({s : ℕ |
          Erdos423.IsConsecutiveBlockSum a (m + 1) s}).Finite := by
      apply (Set.finite_Iic
        (∑ t ∈ Icc 1 m, a t)).subset
      rintro s ⟨i, j, hi, hij, hj, rfl⟩
      change (∑ l ∈ Icc i j, a l) ≤ (∑ t ∈ Icc 1 m, a t)
      apply Finset.sum_le_sum_of_subset
      intro t ht
      rw [mem_Icc] at ht ⊢
      omega
    exact Set.ncard_le_ncard hs hf
  exact hscale b d hsub
    ((1101 : ℝ) / 688 - η)
    (hconv p hp hc η hη)

end OMA.R_Erdos423_erdos_423_variants_upper_bound_R1_H1_R1
