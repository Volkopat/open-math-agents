import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

/-!
# Boundedness of the number of decimal generators of a prime

Source: https://oeis.org/A107740, Reinhard Zumkeller.
The n-th entry counts the nonnegative m for which m plus its decimal digit
sum equals the n-th prime. For a prime p every such m is less than p.
Ranging over all primes thus gives the original boundedness conjecture,
independently of the convention for indexing the primes.
-/

namespace OMA.S_oeis_a107740

def generatorCount (p : ℕ) : ℕ :=
  ((Finset.range p).filter (fun m => m + (Nat.digits 10 m).sum = p)).card

theorem main : ∃ B : ℕ, ∀ p : ℕ, p.Prime → generatorCount p ≤ B := by
  sorry

end OMA.S_oeis_a107740
