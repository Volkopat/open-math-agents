import Mathlib

/-!
# A089948: Smallest prime factor of the concatenation of the first n odd primes

Source: https://oeis.org/A089948
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Smallest prime factor of the concatenation of the first n odd primes.
Conjecture: Beyond 3 (i.e., for all n >= 2), the concatenation of the first n
odd primes produces only composite numbers.
-/

namespace OMA.S_oeis_a089948

/-- Base-10 concatenation of two natural numbers. -/
def concat (x y : ℕ) : ℕ :=
  x * 10 ^ (Nat.digits 10 y).length + y

/-- Concatenation of the first n odd primes (3, 35, 357, 35711, ...). -/
noncomputable def oddPrimeConcat : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | n + 1 => concat (oddPrimeConcat n) (Nat.nth Nat.Prime (n + 1))

theorem main :
    ∀ n : ℕ, 2 ≤ n → ¬ Nat.Prime (oddPrimeConcat n) := by
  sorry

end OMA.S_oeis_a089948
