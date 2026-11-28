import Mathlib

/-!
# A333197: Nonprime numbers k such that each nonprime divisor of k is 1 away from a prime number.

Source: https://oeis.org/A333197
Credit: @ceejcake

Conjecture (OEIS A333197, Michel Lagneau, Mar 11 2020): except for `a(n) = 4, 8, 16` and `32`,
`a(n)` is of the form `2^i*p^j` with `p = 3, 5, 7, 11, 19, 23, 29, 31, ...` (`{A120628}` minus `{2}`).

Formalization notes:
* `IsTerm k` says that `k` is a term of A333197: `k ≥ 1`, `k` is not prime, and every nonprime
  divisor `d` of `k` is 1 away from a prime, i.e. `d + 1` or `d - 1` is prime. (In `ℕ`, `d - 1` is
  truncated subtraction; this is harmless since `0` is not prime and every divisor is `≥ 1`.)
  The term `1` belongs to the sequence: its only divisor `1` is 1 away from the prime `2`.
* `IsA120628 p` says that `p` is in A120628: `p` is prime and `2 * p` is 1 away from a prime,
  i.e. `2 * p - 1` or `2 * p + 1` is prime.
* The form `2^i*p^j` is read with exponents `i, j ≥ 0` allowed to be zero. This is the reading under
  which every listed data term is covered (the term `1 = 2^0 * p^0`, which is not among the listed
  exceptions, would not be covered if `j ≥ 1` were required). With this reading the exceptions
  `4, 8, 16, 32` are kept exactly as stated, as extra disjuncts.
* Initial terms: `1, 4, 6, 8, 10, 12, 14, 16, 20, 22, 24, 28, 32, 38, 40, 44, 46, 48, 58, 62, ...`.
-/

namespace OMA.S_oeis_a333197

/-- `IsTerm k`: `k` is a term of A333197, a nonprime number `k ≥ 1` such that each nonprime divisor
`d` of `k` is 1 away from a prime (`d + 1` or `d - 1` is prime). -/
def IsTerm (k : ℕ) : Prop :=
  1 ≤ k ∧ ¬ k.Prime ∧ ∀ d ∈ k.divisors, ¬ d.Prime → ((d + 1).Prime ∨ (d - 1).Prime)

/-- `IsA120628 p`: `p` is a term of A120628, a prime whose double is 1 away from a prime. -/
def IsA120628 (p : ℕ) : Prop :=
  p.Prime ∧ ((2 * p - 1).Prime ∨ (2 * p + 1).Prime)

/-- OEIS A333197 conjecture: every term other than `4, 8, 16, 32` has the form `2 ^ i * p ^ j`
(with `i, j ≥ 0`) for some `p` in A120628 with `p ≠ 2`. -/
theorem main : ∀ k : ℕ, IsTerm k →
    k = 4 ∨ k = 8 ∨ k = 16 ∨ k = 32 ∨
      ∃ i j p : ℕ, IsA120628 p ∧ p ≠ 2 ∧ k = 2 ^ i * p ^ j := by
  sorry

end OMA.S_oeis_a333197
