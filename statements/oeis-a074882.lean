import Mathlib

/-!
# OEIS A074882: fewer than n integers in 1..sigma(n) are coprime to n when n is not a prime power

Source: https://oeis.org/A074882 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (offset 1): Number of integers in {1, 2, ..., sigma(n)} that are coprime to n.
Data: 1, 2, 3, 4, 5, 4, 7, 8, 9, 7, 11, 9, ... Comment (Robert Israel, Aug 10 2026): a(n) <= n,
with equality if n is in A000961. Conjecture: a(n) < n if n is not in A000961.

Formalization notes:
* sigma(n) is the sum of the divisors of n, `ArithmeticFunction.sigma 1 n`.
* A000961 is the sequence of powers of primes, 1 and p^k with p prime and k >= 1 (`InA000961`).
* The sequence has offset 1, so `main` is stated for n >= 1.
* Controls proved in the proof file: a(6) = 4, a(10) = 7, a(12) = 9 and a(8) = 8.
-/

namespace OMA.S_oeis_a074882

open Finset

/-- A074882: the number of integers in {1, ..., sigma(n)} that are coprime to n. -/
def a (n : ℕ) : ℕ := ((Icc 1 (ArithmeticFunction.sigma 1 n)).filter (fun k => Nat.Coprime k n)).card

/-- A000961: 1 and the prime powers p^k with k >= 1. -/
def InA000961 (n : ℕ) : Prop := n = 1 ∨ ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p ^ k

/-- Israel's conjecture: a(n) < n for every n >= 1 that is not in A000961. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ¬ InA000961 n → a n < n := by
  sorry

end OMA.S_oeis_a074882
