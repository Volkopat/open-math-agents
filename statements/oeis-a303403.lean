import Mathlib

/-!
# A303403: Even numbers that are not the sum of two prime-indexed primes.

Source: https://oeis.org/A303403
Credit: @luciusacarr

Data: 2, 4, 12, 18, 24, 26, 30, 32, 38, 40, 50, 54, 56, 60, ...

The entry says: Bayless et al. conjectured that every even number larger than 80612 is the sum
of two prime-indexed primes. If the conjecture is true then this sequence is finite with 733
terms. `main` states the conjecture of Bayless et al.

Reading of the source:
* A prime-indexed prime (A006450) is `prime(p)` with `p` prime, `prime(1) = 2` being the first
  prime. With Mathlib's 0-indexed `Nat.nth Nat.Prime`, `prime(p) = Nat.nth Nat.Prime (p - 1)`.
  Example: 20 = 17 + 3 = prime(7) + prime(2).
* The two summands may be equal.
* With this reading the even numbers up to 200000 that are not such sums number 733, the largest
  being 80612 (checked numerically), as the entry says.
-/

namespace OMA.S_oeis_a303403

/-- `q` is a prime-indexed prime: `q = prime(p)` for a prime `p` (1-indexed primes). -/
def IsPrimeIndexedPrime (q : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ q = Nat.nth Nat.Prime (p - 1)

theorem main :
    -- Every even number larger than 80612 is the sum of two prime-indexed primes.
    ∀ n : ℕ, Even n → 80612 < n →
      ∃ a b : ℕ, IsPrimeIndexedPrime a ∧ IsPrimeIndexedPrime b ∧ n = a + b := by
  sorry

end OMA.S_oeis_a303403
