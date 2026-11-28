import Mathlib

/-!
# A214342: Count of the decimal descendants of the n-th prime.

Source: https://oeis.org/A214342
Credit: @luciusacarr

Data: 23, 22, 11, 23, 1, 14, 4, 40, 15, 6, 7, 13, 1, 14, 5, 0, 9, 16, 11, 4, ... (offset 1).

Conjecture (from the entry): no terms bigger than 35 after a(8) = 40. `main` states it.

Reading of the source:
* A prime `q` is a direct decimal descendant of a prime `p` if `q = 10p + k` with `0 ≤ k ≤ 9`.
  a(n) counts the direct descendants of the n-th prime that are prime, plus their prime direct
  descendants, and so on: the primes `q` reachable from `p` by a chain of one or more steps
  `a ↦ 10a + k` (`0 ≤ k ≤ 9`) in which every number reached is prime. This is the transitive
  closure `Relation.TransGen` of the one-step relation (example: 5 has the eleven descendants 53,
  59, 593, 599, 5939, 59393, 59399, 593933, 593993, 5939333, 59393339). The first 29 terms were
  recomputed from this reading.
* The n-th prime is `Nat.nth Nat.Prime (n - 1)` (Mathlib's `Nat.nth` is 0-indexed), so "after
  a(8)" is every index `n ≥ 9`, i.e. every 0-indexed `i ≥ 8`.
* "No term bigger than 35" is stated as: the set of descendants is finite and has at most 35
  elements (an infinite set of descendants would be a term bigger than 35).
-/

namespace OMA.S_oeis_a214342

/-- `b` is a prime direct decimal descendant of `a`. -/
def Step (a b : ℕ) : Prop := b.Prime ∧ ∃ k : ℕ, k ≤ 9 ∧ b = 10 * a + k

/-- The decimal descendants of `p`: primes reachable from `p` by one or more steps. -/
def descendants (p : ℕ) : Set ℕ := {q | Relation.TransGen Step p q}

theorem main :
    -- No terms bigger than 35 after a(8) = 40.
    ∀ i : ℕ, 8 ≤ i → (descendants (Nat.nth Nat.Prime i)).Finite ∧
      (descendants (Nat.nth Nat.Prime i)).ncard ≤ 35 := by
  sorry

end OMA.S_oeis_a214342
