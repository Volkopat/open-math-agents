import Mathlib

/-!
A085114: Binary expansion of Sum 1/(p*2^p) where p runs through the set of Artin primes (primes with primitive root 2).

Source: https://oeis.org/A085114
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

David H. Bailey and Richard E. Crandal conjectured that this constant is 2-normal.
-/

namespace OMA.S_oeis_a085114

open Classical Filter Topology

def IsArtinPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ orderOf (2 : ZMod p) = p - 1

noncomputable def artinConstant : ℝ :=
  ∑' p : ℕ, if IsArtinPrime p then (1 : ℝ) / ((p : ℝ) * (2 : ℝ) ^ p) else 0

noncomputable def fracDigit (b : ℕ) (x : ℝ) (j : ℕ) : ℕ :=
  Int.toNat (⌊(b : ℝ) ^ (j + 1) * x⌋ % (b : ℤ))

noncomputable def IsNormalInBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (w : Fin k → Fin b),
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun i => ∀ j : Fin k, fracDigit b x (i + j.val) = (w j).val).card : ℝ) /
          (N : ℝ))
      atTop (𝓝 ((1 : ℝ) / (b : ℝ) ^ k))

theorem main : IsNormalInBase 2 artinConstant := by
  sorry

end OMA.S_oeis_a085114
