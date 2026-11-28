import Mathlib

/-!
# A328202: the gcd of the inner binomial coefficients C(n, k), 2 <= k <= n - 2

Source: https://oeis.org/A328202 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A328202, offset 4: a(n) is the greatest common divisor of all the numbers in row n of
Pascal's triangle excluding 1 and n. Data
6, 10, 5, 7, 14, 6, 3, 11, 11, 13, 13, 1, 2, 34, 17, 19, 19, 1, 1, 23, 23, 5, 5, 3, 3, 29, 29, ...
Entry A014963: a(n) = p if n is a power p^k of a prime p with k >= 1, and a(n) = 1 otherwise.

Comments, from Robert Israel, Oct 16 2019: If p is a Fermat prime > 3, a(p)=2*p. If p is a
Mersenne prime, a(p+1)=2*p. Conjecture: these are the only cases where a(n)>n.
Formula section: a(n) = A014963(n) * A014963(n - 1) (conjecture). - Jon Maiga, Oct 08 2019

Formalization notes.
* Row n without the entries 1 and n is C(n, k) for 2 <= k <= n - 2, and `a n` is the gcd of
  these numbers (`Finset.gcd` on `Finset.Icc 2 (n - 2)`). The offset is 4.
* `E n` is A014963(n): the least prime factor of n if n is a prime power, and 1 otherwise.
* `main` is the conjunction of the two conjectures for every n >= 4. A Fermat prime is a prime
  of the form 2^(2^k) + 1. The number n - 1 is a Mersenne prime when n - 1 is prime and n is a
  power of 2.
-/

namespace OMA.S_oeis_a328202

/-- A328202(n): the gcd of the binomial coefficients C(n, k) for 2 ≤ k ≤ n - 2. -/
def a (n : ℕ) : ℕ := (Finset.Icc 2 (n - 2)).gcd (fun k => n.choose k)

/-- A014963(n): the prime p if n is a power p^k with k ≥ 1, and 1 otherwise. -/
noncomputable def E (n : ℕ) : ℕ :=
  open Classical in if IsPrimePow n then n.minFac else 1

/-- Maiga's conjecture a(n) = A014963(n) * A014963(n - 1), and Israel's conjecture: a(n) > n
exactly when n is a Fermat prime or n - 1 is a Mersenne prime. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    a n = E n * E (n - 1) ∧
    (n < a n ↔ (n.Prime ∧ ∃ k : ℕ, n = 2 ^ 2 ^ k + 1) ∨ ((n - 1).Prime ∧ ∃ k : ℕ, n = 2 ^ k)) := by
  sorry

end OMA.S_oeis_a328202
