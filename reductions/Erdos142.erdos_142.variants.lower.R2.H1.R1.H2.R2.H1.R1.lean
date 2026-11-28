import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2
import Mathlib

/-!
# Covering a four-term-progression-free set by three-term-progression-free sets

The finite combinatorial question is whether a four-term-progression-free set
of density α can always be covered by O(α^(-1/2)) three-term-progression-free
sets. Such a cover gives the comparison exponent 2/3: if x is the size of the
set, y is the three-term extremal number, and q is the cover size, then
x ≤ qy and q²x ≤ D³N imply x³ ≤ D³Ny².
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1

open Erdos142 Filter

/-- A square-root bound for the cover number above the sparse range. The sets in a cover may overlap. -/
def H1 : Prop :=
  ∃ D : ℝ, 2 ≤ D ∧ ∀ᶠ N : ℕ in atTop,
    ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → (S : Set ℕ).IsAPOfLengthFree 4 → N < S.card ^ 2 →
    ∃ (q : ℕ) (B : Fin q → Finset ℕ),
      S ⊆ Finset.univ.biUnion B ∧
      (∀ i, B i ⊆ Finset.Icc 1 N ∧ ((B i : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3) ∧
      (q : ℝ) ^ 2 * S.card ≤ D ^ 3 * N

/-- Each member of a cover contributes at most the three-term extremal number. -/
def H2 : Prop :=
  ∀ (N q : ℕ) (S : Finset ℕ) (B : Fin q → Finset ℕ),
    S ⊆ Finset.univ.biUnion B →
    (∀ i, B i ⊆ Finset.Icc 1 N ∧ ((B i : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3) →
    S.card ≤ q * r 3 N

/-- Sparse sets admit a cover with an absolute cost bound. -/
def H3 : Prop :=
  ∀ (N : ℕ) (S : Finset ℕ), S ⊆ Finset.Icc 1 N → (S : Set ℕ).IsAPOfLengthFree 4 → S.card ^ 2 ≤ N →
    ∃ (q : ℕ)(B : Fin q → Finset ℕ),
      S ⊆ Finset.univ.biUnion B ∧
      (∀ i, B i ⊆ Finset.Icc 1 N ∧ ((B i : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3) ∧
      (q : ℝ) ^ 2 * S.card ≤ 4 * N

lemma compare_by_cover {x y N D q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hN : 0 < N) (hD : 0 < D)
    (hcard : x ≤ q * y) (hcost : q ^ 2 * x ≤ D ^ 3 * N) :
    x ≤ D * N * (y / N) ^ (2 / 3 : ℝ) := by
  have hyN : 0 ≤ y / N := div_nonneg hy hN.le
  have hpower : ((y / N) ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = (y / N) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast ((y / N) ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul hyN]
    norm_num
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
  calc
    x ^ 3 = x * x ^ 2 := by ring
    _ ≤ x * (q * y) ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hcard 2) hx
    _ = q ^ 2 * x * y ^ 2 := by ring
    _ ≤ D ^ 3 * N * y ^ 2 := mul_le_mul_of_nonneg_right hcost (sq_nonneg y)
    _ = (D * N * (y / N) ^ (2 / 3 : ℝ)) ^ 3 := by
      rw [mul_pow, hpower]
      field_simp

theorem main : H1 → H2 → H3 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2.H1 := by
  intro hcover hpigeon hsparse
  obtain ⟨D, hD, hlarge⟩ := hcover
  refine ⟨2 / 3, D, by norm_num, by linarith, ?_⟩
  filter_upwards [hlarge, eventually_gt_atTop 0] with N hc hN
  obtain ⟨S, hS, hfree, hcard⟩ :=
    OMA.R_Erdos142_erdos_142_variants_lower_R2.extremizer (k := 4) (by decide) N
  obtain ⟨q, B, hsub, hB, hcost⟩ : ∃ (q : ℕ)(B : Fin q → Finset ℕ),
      S ⊆ Finset.univ.biUnion B ∧
      (∀ i, B i ⊆ Finset.Icc 1 N ∧ ((B i : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3) ∧
      (q : ℝ) ^ 2 * S.card ≤ D ^ 3 * N := by
    by_cases hdense : N < S.card ^ 2
    · exact hc S hS hfree hdense
    · obtain ⟨q, B, hsub, hB, hcost⟩ := hsparse N S hS hfree (Nat.le_of_not_gt hdense)
      refine ⟨q, B, hsub, hB, hcost.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
      exact (show (4 : ℝ) ≤ 2 ^ 3 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hD 3)
  have hp := hpigeon N q S B hsub hB
  rw [hcard] at hp hcost
  exact compare_by_cover (q := (q : ℝ)) (by positivity) (by positivity) (by exact_mod_cast hN)
    (by linarith) (by exact_mod_cast hp) hcost

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1
