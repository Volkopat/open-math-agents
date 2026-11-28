import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

-- Reduction Erdos1160.erdos_1160.variants.sum.R3.H1.R2.H1.R1 of step Erdos1160.erdos_1160.variants.sum.R3.H1.R2.H1
-- Credit: @TheLittleOne1234

/- The comparison between g(2^a) and g(2^m) for a ≤ m follows from an upper bound with
quadratic error at a and Higman's lower bound at m.

H1 is, word for word, the statement of step Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2
(the desk lists R1.H2 as solved through it: reduction R1.H2.R1.H2.R2 with merged proofs of its
four hypotheses by @kamaleshanantha, PRs 2283, 2310, 2379, 2452). The same statement is also step
R2.H1.R1.H2.R1.H2.

H2 is, word for word, the statement of step Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H1.R1.H3
(merged proof proofs/Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H1.R1.H3.lean, @KevinBigham).

For a below the threshold of H1 the finitely many values g(2^a)^27 go into the constant. -/

open Filter Finset Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R2_H1_R1

def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop, g (2^m)^27 * 2 ^ (9 * m^2) ≤ 2 ^ (2 * m^3)

def H2 : Prop := ∀ m : ℕ, 3 ≤ m → 2^(2*m^3) ≤ g (2^m)^27 * 2^(12*m^2)

theorem upper_all (h1 : H1) : ∃ K : ℕ, ∀ a : ℕ, g (2^a)^27 ≤ 2^(2*a^3 + K) := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp h1
  refine ⟨∑ a ∈ range A, g (2^a)^27, fun a => ?_⟩
  by_cases ha : A ≤ a
  · calc g (2^a)^27 ≤ g (2^a)^27 * 2 ^ (9 * a^2) := Nat.le_mul_of_pos_right _ (by positivity)
      _ ≤ 2 ^ (2 * a^3) := hA a ha
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  · have hmem : a ∈ range A := mem_range.mpr (by omega)
    calc g (2^a)^27 ≤ ∑ a ∈ range A, g (2^a)^27 :=
          single_le_sum (f := fun a => g (2^a)^27) (fun _ _ => Nat.zero_le _) hmem
      _ ≤ 2 ^ (∑ a ∈ range A, g (2^a)^27) := Nat.lt_two_pow_self.le
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R2.H1 := by
  intro h1 h2
  obtain ⟨K, hK⟩ := upper_all h1
  refine ⟨12 + K, fun a m hm _ => ?_⟩
  calc 2^(2*m^3) * g (2^a)^27 ≤ (g (2^m)^27 * 2^(12*m^2)) * 2^(2*a^3 + K) :=
        Nat.mul_le_mul (h2 m hm) (hK a)
    _ = g (2^m)^27 * 2^(12*m^2 + (2*a^3 + K)) := by rw [Nat.mul_assoc, ← pow_add]
    _ ≤ g (2^m)^27 * 2^(2*a^3 + (12 + K)*(m+1)^2) := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by decide)
        nlinarith only [Nat.zero_le m, Nat.zero_le K]

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R2_H1_R1
