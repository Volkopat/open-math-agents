import Mathlib

/-!
# A068819: n!/((n+1)*(n+2)*...*(n+k)) where k is largest value that gives an integer quotient.

Source: https://oeis.org/A068819
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a068819

def nextPrime (n : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (n + 1))

def productBeforeNextPrime (n : ℕ) : ℕ :=
  (Finset.Icc 1 (nextPrime n - n - 1)).prod fun j => n + j

theorem main : ∀ n : ℕ, 3 < n →
    productBeforeNextPrime n ∣ Nat.factorial n := by
  sorry

end OMA.S_oeis_a068819
