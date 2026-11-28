import Mathlib

/-!
# A321644 and the twin prime conjecture

Source: https://oeis.org/A321644
Credit: @etaubman

The primes dividing a term may belong to different twin pairs.
-/

namespace OMA.S_oeis_a321644

/-- Lower endpoints of twin prime pairs. -/
def lowerTwins : Set ℕ := {p | p.Prime ∧ (p + 2).Prime}

/-- Both members of all twin prime pairs. -/
def twinPrimes : Set ℕ := lowerTwins ∪ (fun p : ℕ => p + 2) '' lowerTwins

/-- The original squarefree, odd, composite and prime-factor conditions. -/
def terms : Set ℕ := {n | Squarefree n ∧ Odd n ∧ 1 < n ∧ ¬n.Prime ∧
    ∀ q : ℕ, q.Prime → q ∣ n → q ∈ twinPrimes}

theorem main : terms.Infinite ↔ lowerTwins.Infinite := by
  sorry

end OMA.S_oeis_a321644
