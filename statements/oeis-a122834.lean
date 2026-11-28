import Mathlib

/-!
# A122834: Primes in the new Mersenne conjecture; odd primes of the form 2^k+-1 or 4^k+-3

Source: https://oeis.org/A122834
Credit: @sobrien032

The terms are the odd primes `p` of the form `2^k ± 1` or `4^k ± 3` (3, 5, 7, 13, 17, 19, 31, 61,
67, 127, ...). The entry's comment: "Let p be a prime in this sequence. Call q=2^p-1 and
r=(2^p+1)/3. The new Mersenne conjecture implies that either q and r are both prime or both
composite."

The new Mersenne conjecture (Bateman, Selfridge and Wagstaff, 1989) says: for every odd natural
number `p`, if two of the following three conditions hold, then so does the third:
(a) `p = 2^k ± 1` or `p = 4^k ± 3` for some natural number `k`;
(b) `2^p - 1` is prime;
(c) `(2^p + 1)/3` is prime.
Below, `p = 2^k - 1` and `p = 4^k - 3` are written `p + 1 = 2^k` and `p + 3 = 4^k`. For odd `p`,
`3` divides `2^p + 1`, so `(2^p + 1) / 3` is exact. A composite number is a number `> 1` that is
not prime.
-/

namespace OMA.S_oeis_a122834

/-- Condition (a): `p = 2^k ± 1` or `p = 4^k ± 3` for some natural number `k`. -/
def SpecialForm (p : ℕ) : Prop :=
  ∃ k : ℕ, p + 1 = 2 ^ k ∨ p = 2 ^ k + 1 ∨ p + 3 = 4 ^ k ∨ p = 4 ^ k + 3

/-- The new Mersenne conjecture: for every odd `p`, any two of (a) `SpecialForm p`,
(b) `2^p - 1` is prime, (c) `(2^p + 1)/3` is prime, imply the third. -/
def NewMersenneConjecture : Prop :=
  ∀ p : ℕ, Odd p →
    ((SpecialForm p ∧ (2 ^ p - 1).Prime) → ((2 ^ p + 1) / 3).Prime) ∧
    ((SpecialForm p ∧ ((2 ^ p + 1) / 3).Prime) → (2 ^ p - 1).Prime) ∧
    (((2 ^ p - 1).Prime ∧ ((2 ^ p + 1) / 3).Prime) → SpecialForm p)

/-- The entry's claim: under the new Mersenne conjecture, for every term `p` (an odd prime of the
form `2^k ± 1` or `4^k ± 3`), `q = 2^p - 1` and `r = (2^p + 1)/3` are both prime or both
composite. -/
theorem main : NewMersenneConjecture →
    ∀ p : ℕ, p.Prime → Odd p → SpecialForm p →
      ((2 ^ p - 1).Prime ∧ ((2 ^ p + 1) / 3).Prime) ∨
      ((1 < 2 ^ p - 1 ∧ ¬ (2 ^ p - 1).Prime) ∧
        (1 < (2 ^ p + 1) / 3 ∧ ¬ ((2 ^ p + 1) / 3).Prime)) := by
  sorry

end OMA.S_oeis_a122834
