import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1
import Mathlib.GroupTheory.Solvable

/- Credit: @michelzerasafadaum-gif. The odd-order theorem and a Sylow-profile count for solvable groups suffice.
The solvable bound used below is restricted to odd orders and costs a square in the binary logarithm. The earlier reduction in PR 9018 used a stronger bound in terms of the largest prime exponent for all orders. -/
open Erdos1160 CategoryTheory
namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2

/-- The Feit-Thompson odd-order theorem. -/
def H1 : Prop := ∀ G : FiniteGrp.{0}, Odd (Nat.card G) → Group.IsSolvable G

/-- Count only isomorphism classes represented by solvable groups. -/
def H2 : Prop := ∃ E : ℕ, ∀ q r : ℕ, Odd q → q < 2^r →
  (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G}).ncard ≤
    2^(E*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p)

theorem main : H1 → H2 →
    OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1.H3 := by
  intro odd_order count
  obtain ⟨E,hE⟩ := count
  refine ⟨E,?_⟩
  intro q r odd lt
  have eq : {G : FiniteGrp.{0} | Nat.card G=q} =
      {G : FiniteGrp.{0} | Nat.card G=q ∧ Group.IsSolvable G} := by
    ext G
    exact ⟨fun h => ⟨h,odd_order G (h.symm ▸ odd)⟩,fun h => h.1⟩
  change (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G=q}).ncard ≤ _
  rw [eq]
  exact hE q r odd lt

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2
