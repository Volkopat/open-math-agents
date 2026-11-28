import Mathlib

/-!
# OEIS A281648: numerator of Bernoulli(2n) mod n equals n-1 only for n = 6, 10 and powers of 2

Source: https://oeis.org/A281648 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-fable-5-2), submitted by @jleguina.

Entry, offset 1: (Numerator of Bernoulli(2*n)) read mod n, with the formula a(n) = A000367(n) mod n.
Comment (Seiichi Manyama, Jan 27 2017): Conjecture: a(n) == n-1 (mod n) if only if n = 6, 10 or
n = 2^k for k >= 0. This is true for n <= 1024.

Formalization notes:
* The numerator is the signed numerator of the Bernoulli number in lowest terms (A000367), and the
  residue is taken in {0, ..., n-1}; `%` on integers with a positive modulus does that.
* Since a(n) is already reduced mod n, the condition a(n) == n-1 (mod n) is a(n) = n-1.
* Controls from the entry: the terms for n = 1..8 are 0, 1, 1, 3, 0, 5, 0, 7 (for example
  Bernoulli(8) = -1/30 gives a(4) = 3).
-/

namespace OMA.S_oeis_a281648

/-- A281648(n): the numerator of Bernoulli(2n), read mod n. -/
def a (n : ℕ) : ℤ := (bernoulli (2 * n)).num % n

/-- Manyama's conjecture: a(n) = n-1 if and only if n = 6, n = 10 or n is a power of 2. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = (n : ℤ) - 1 ↔ (n = 6 ∨ n = 10 ∨ ∃ k : ℕ, n = 2 ^ k)) := by
  sorry

end OMA.S_oeis_a281648
