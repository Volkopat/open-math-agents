import Mathlib

/-!
# OEIS A337868: a(n) = phi(n) + 1 exactly for the primes and the squares of primes

Source: https://oeis.org/A337868 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (José María Grau Ribas, Sep 27 2020), offset 1: Number of distinct residues of x^r (mod n),
x=0..n-1, r=2, ..., n. The formula section states: For n > 1, a(n) >= A000010(n) + 1 as all
invertible elements of Z/nZ are powers, as is 0. (Conjecture: equality holds exactly for A000430,
the primes and squares of primes.) - Charles R Greathouse IV, Dec 23 2022

Formalization notes:
* a(n) is the number of distinct values x^r mod n with 0 <= x <= n-1 and 2 <= r <= n.
* A000010 is Euler's totient function; A000430 is the sequence of the primes and the squares of
  primes.
* `main` is the conjecture in parentheses, for every n > 1: a(n) = phi(n) + 1 if and only if n is
  a prime or the square of a prime. The inequality before it is stated with its reason in the
  entry and is not part of the conjecture.
* Controls: the definitions give a(1..26) = 0, 2, 3, 3, 5, 6, 7, 6, 7, 10, 11, 9, 13, 14, 15, 11,
  17, 14, 19, 15, 21, 22, 23, 17, 21, 26, as in the entry.
-/

namespace OMA.S_oeis_a337868

open Finset

/-- The set of residues x^r mod n, x < n, 2 <= r <= n. -/
def R (n : ℕ) : Finset ℕ := ((range n ×ˢ Icc 2 n).image (fun xr => xr.1 ^ xr.2 % n))

/-- A337868(n): the number of these residues. -/
def a (n : ℕ) : ℕ := (R n).card

/-- Greathouse's conjecture: for n > 1, a(n) = phi(n) + 1 iff n is a prime or a prime squared. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n → (a n = n.totient + 1 ↔ ∃ p : ℕ, p.Prime ∧ (n = p ∨ n = p ^ 2)) := by
  sorry

end OMA.S_oeis_a337868
