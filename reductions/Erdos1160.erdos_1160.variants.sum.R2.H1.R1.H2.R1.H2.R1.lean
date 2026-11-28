import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1_H2_R1
import Mathlib.GroupTheory.Frattini

-- Credit: @LordMike
-- Port of reductions/Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.lean by @kamaleshanantha (PR #626) onto the identical hypothesis statement Erdos1160.erdos_1160.variants.sum.R2.H1.R1.H2.R1.H2.

open Filter CategoryTheory Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1_H2_R1_H2_R1

/-- Groups with central elementary abelian Frattini subgroup. -/
def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop,
    (2 * (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^m ∧
        frattini G ≤ Subgroup.center G ∧ (∀ x : frattini G, x*x = 1)}).ncard)^27 *
        2^(9*m^2) ≤ 2^(2*m^3)

/-- Groups whose Frattini subgroup fails at least one of the two conditions. -/
def H2 : Prop :=
  ∀ᶠ m : ℕ in atTop,
    (2 * (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^m ∧
        ¬ (frattini G ≤ Subgroup.center G ∧ (∀ x : frattini G, x*x = 1))}).ncard)^27 *
        2^(9*m^2) ≤ 2^(2*m^3)

lemma union_bound {α : Type*} (A B : Set α) (t u : ℕ)
    (ha : (2*A.ncard)^27*t ≤ u) (hb : (2*B.ncard)^27*t ≤ u) :
    (A∪B).ncard^27*t ≤ u := by
  have hs := Set.ncard_union_le A B
  rcases le_total A.ncard B.ncard with h | h
  · exact (Nat.mul_le_mul_right t (Nat.pow_le_pow_left (by omega : (A∪B).ncard ≤ 2*B.ncard) 27)).trans hb
  · exact (Nat.mul_le_mul_right t (Nat.pow_le_pow_left (by omega : (A∪B).ncard ≤ 2*A.ncard) 27)).trans ha

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1_H2_R1.H2 := by
  intro hmain hrest
  unfold H1 at hmain
  unfold H2 at hrest
  unfold OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1_H2_R1.H2
  filter_upwards [hmain,hrest] with m hm hr
  let P (G : FiniteGrp.{0}) := frattini G ≤ Subgroup.center G ∧ (∀ x : frattini G, x*x=1)
  let q := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0})
  have partition : q '' {G : FiniteGrp.{0} | Nat.card G = 2^m} =
      (q '' {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ P G}) ∪
      (q '' {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ ¬ P G}) := by
    ext c
    constructor
    · rintro ⟨G,h,e⟩
      by_cases hP : P G
      · exact Or.inl ⟨G,⟨h,hP⟩,e⟩
      · exact Or.inr ⟨G,⟨h,hP⟩,e⟩
    · rintro (⟨G,⟨h,_⟩,e⟩ | ⟨G,⟨h,_⟩,e⟩) <;> exact ⟨G,h,e⟩
  change (q '' {G : FiniteGrp.{0} | Nat.card G = 2^m}).ncard^27 * 2^(9*m^2) ≤ _
  rw [partition]
  exact union_bound _ _ _ _ hm hr

end OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1_H2_R1_H2_R1
