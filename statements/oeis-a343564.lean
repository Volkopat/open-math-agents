import Mathlib

/-!
# A343564: a(n) is the sum of 2*n mod p for primes p such that 2*n-p is prime.

Source: https://oeis.org/A343564
Credit: @azmiozgen

Conjecture (from the entry): the only n for which a(n) <= n are 1, 2, 3, 5, 7, 11, 19, and 31.

Formalization notes:
* The sum runs over primes p ≤ 2n with 2n - p prime (p < 2n since 0 is not prime).
* Stated for every n ≥ 1 as: a(n) ≤ n iff n is one of the eight listed values.
* Controls (computed): a(1..25) = 0, 0, 0, 5, 4, 7, 5, 10, 19, 18, 11, 32, 17, 25, 45, 24, 25, 56, 10,
  45, 66, 32, 39, 96, 68, as in the entry; for n < 5000, a(n) ≤ n exactly for the listed n.
-/

namespace OMA.S_oeis_a343564

/-- A343564(n). -/
def a (n : ℕ) : ℕ := ∑ p ∈ (Finset.range (2 * n)).filter (fun p => p.Prime ∧ (2 * n - p).Prime), (2 * n) % p

/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → (a n ≤ n ↔ n ∈ ({1, 2, 3, 5, 7, 11, 19, 31} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a343564
