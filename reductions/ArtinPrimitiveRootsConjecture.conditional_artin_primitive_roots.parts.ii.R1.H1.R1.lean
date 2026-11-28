import OMAReductions.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_ii_R1

-- Credit: @marcusbuffett

namespace OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_ii_R1_H1_R1

open Finset Set Filter
open scoped Classical

/-- Chebotarev input: simultaneous complete splitting at the squarefree levels
has density the reciprocal of the Kummer field degree. -/
def H1 : Prop := ∀ a a₀ b : ℤ, a = a₀ * b^2 → (∀ n m, m ≠ 1 → a ≠ n^m) →
  Squarefree a₀ → ¬a₀ ≡ 1 [ZMOD 4] → ∀ P : Finset Nat.Primes,
  {p : ℕ | (p.Prime ∧ (a : ZMod p) ≠ 0) ∧ ∀ q ∈ P, (q.val ∣ p - 1 ∧ (a : ZMod p) ^ ((p-1)/q.val) = 1)}.HasDensity
    (∏ q ∈ P, (1 / ((q.val : ℝ) * (q.val - 1 : ℝ)))) {p | p.Prime}

/-- The finite sieve: independent joint event densities imply the complementary product. -/
def H2 : Prop := ∀ (A R : Set ℕ) (E : Nat.Primes → ℕ → Prop) (w : Nat.Primes → ℝ),
  (∀ P : Finset Nat.Primes, {n ∈ A | ∀ q ∈ P, E q n}.HasDensity
    (∏ q ∈ P, w q) R) →
  ∀ P : Finset Nat.Primes, {n ∈ A | ∀ q ∈ P, ¬ E q n}.HasDensity
    (∏ q ∈ P, (1-w q)) R

theorem main : H1 → H2 → OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_ii_R1.H1 := by
  intro joint sieve a a₀ b ha hn hs hd P
  have h := sieve {p : ℕ | p.Prime ∧ (a : ZMod p) ≠ 0} {p | p.Prime}
    (fun q p => q.val ∣ p - 1 ∧ (a : ZMod p) ^ ((p-1)/q.val) = 1)
    (fun q => 1 / ((q.val : ℝ) * (q.val - 1 : ℝ))) (joint a a₀ b ha hn hs hd) P
  simpa only [Set.mem_setOf_eq, not_and, and_assoc] using h

end OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_ii_R1_H1_R1
