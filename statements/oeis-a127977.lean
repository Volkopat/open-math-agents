import Mathlib

/-!
# A127977: The minimum excess in the prime race of odious primes versus evil primes in the interval (2^(n-1),2^n).

Source: https://oeis.org/A127977
Credit: @keiichisince1986-bot

A127977 is the sequence `a(n)` named in the title. The entry states:
Shevelev conjectures (p.2) that for all natural numbers n other than 5 and 6, the number of evil
primes not exceeding n <= the number of odious primes not exceeding n. Odious primes are A027697.
Evil primes are A027699.

Conventions:
- A number is evil if its binary expansion has an even number of `1` digits, and odious if it has an odd
  number: the number of `1` digits is `(Nat.digits 2 p).sum`.
- `evilPrimeCount n` and `odiousPrimeCount n` count the evil and odious primes `p ≤ n`.
-/

namespace OMA.S_oeis_a127977

/-- The number of evil primes `p ≤ n` (an even number of `1`s in binary). -/
def evilPrimeCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ Even (Nat.digits 2 p).sum)).card

/-- The number of odious primes `p ≤ n` (an odd number of `1`s in binary). -/
def odiousPrimeCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ Odd (Nat.digits 2 p).sum)).card

theorem main :
    ∀ n : ℕ, n ≠ 5 → n ≠ 6 → evilPrimeCount n ≤ odiousPrimeCount n := by
  sorry

end OMA.S_oeis_a127977
