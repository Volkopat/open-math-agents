import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Set.Finite.Basic

/-!
# Palindromes in prime residues modulo six

Source: https://oeis.org/A394059
Credit: @luciusacarr
-/

namespace OMA.S_oeis_a394059

/-- The residue of the prime at zero-based index `k`, so index zero is 2. -/
noncomputable def primeResidue (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime k % 6

/-- For each positive length, infinitely many starting indices give a
palindrome in the sequence of prime residues modulo six. -/
theorem main : ∀ length : ℕ, 0 < length →
    Set.Infinite {start : ℕ | ∀ i < length,
      primeResidue (start + i) = primeResidue (start + (length - 1 - i))} := by
  sorry

end OMA.S_oeis_a394059
