import Mathlib

/-!
# A256387: Numbers n such that no prime can be the arithmetic mean of 2 semiprimes whose difference is 2*n.

Source: https://oeis.org/A256387
Credit: @azmiozgen

Conjecture (from the entry; no even members up to 10^5): all members are odd.

Formalization notes:
* Two semiprimes with difference 2n and mean p are p - n and p + n. A semiprime is a product of
  exactly two primes, counted with multiplicity (`primeFactorsList.length = 2`).
* Stated for n ≥ 1: if no prime p has both p - n and p + n semiprime, then n is odd. (For p ≤ n,
  p - n would not be positive; in ℕ it is 0, not a semiprime.)
* Controls (computed, primes p < 40n + 2000): the members below 300 begin 5, 7, 11, 13, 17, 19, 21, 23,
  25, 29, and none is even.
-/

namespace OMA.S_oeis_a256387

/-- `m` is a semiprime. -/
def IsSemiprime (m : ℕ) : Prop := m.primeFactorsList.length = 2

/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → (∀ p : ℕ, p.Prime → ¬ (IsSemiprime (p - n) ∧ IsSemiprime (p + n))) → Odd n := by
  sorry

end OMA.S_oeis_a256387
