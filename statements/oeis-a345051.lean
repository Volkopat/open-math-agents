import Mathlib

/-!
# OEIS A345051: the sequence is the disjoint union of A000396 and A166374

Source: https://oeis.org/A345051 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Antti Karttunen, Jun 06 2021), offset 1: Numbers k such that A345048(k) is equal to
A345049(k). Comment: Conjecture: Sequence is a disjoint union of A000396 and A166374, i.e., there
are no terms of any other kind.

The sequences involved, from their entries: A345048(n) = A342001(n) * A051709(n);
A345049(n) = A173557(n) * A345001(n); A342001(n) is the arithmetic derivative of n divided by
A003557(n); A003557(n) is n divided by the largest squarefree divisor of n; A051709(n) =
sigma(n) + phi(n) - 2n; A173557(n) = Product_{primes p dividing n} (p - 1); A345001(n) =
sigma(n) + n' - 2n; n' = A003415(n) is the arithmetic derivative; phi = A000010 is the Euler
totient; sigma = A000203 is the sum of divisors. A000396 lists the perfect numbers, k equal to the
sum of the proper divisors of k. A166374 lists the numbers whose arithmetic derivative is equal to
the Euler totient function, n' = phi(n) (offset 1, data 2, 9, 15, ...).

Formalization notes:
* n' is written in its closed form n * Sum_{p | n} v_p(n)/p (A003415, formula section) as
  Sum_{p | n} v_p(n) * (n / p), each division exact; it gives 0' = 1' = 0, p' = 1 for primes.
* The largest squarefree divisor of n is the product of the primes dividing n (A007947).
* A342001, A051709, A345001, A345048 and A345049 are rational-valued, so that every division in
  the entries is exact and A345001 may be negative (A345001(1) = -1, as in its data); on n >= 1
  they take the integer values listed in the entries. phi is Mathlib's `Nat.totient`.
* A345051 and A166374 are subsets of the positive integers (offset 1); perfect numbers are
  Mathlib's `Nat.Perfect` (sum of proper divisors equals n, and n > 0).
* `main` is the conjecture: A345051 = A000396 union A166374, and A000396, A166374 are disjoint.
* Controls proved in the proof file: 2 and 6 are in A345051 and 1 is not.
-/

namespace OMA.S_oeis_a345051

/-- sigma(n) = A000203(n), the sum of the divisors of n. -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- n' = A003415(n), the arithmetic derivative n * Sum_{p | n} v_p(n) / p, written as
Sum_{p | n} v_p(n) * (n / p) (each division is exact). -/
def deriv (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n.factorization p * (n / p)

/-- A007947(n), the largest squarefree divisor of n: the product of the primes dividing n. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- A003557(n): n divided by the largest squarefree divisor of n. -/
def a003557 (n : ℕ) : ℕ := n / rad n

/-- A342001(n) = A003415(n) / A003557(n). -/
def a342001 (n : ℕ) : ℚ := (deriv n : ℚ) / (a003557 n : ℚ)

/-- A051709(n) = sigma(n) + phi(n) - 2n, with phi = A000010 the Euler totient. -/
def a051709 (n : ℕ) : ℚ := (sigma n : ℚ) + (Nat.totient n : ℚ) - 2 * n

/-- A173557(n) = Product_{primes p dividing n} (p - 1). -/
def a173557 (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, (p - 1)

/-- A345001(n) = sigma(n) + n' - 2n. -/
def a345001 (n : ℕ) : ℚ := (sigma n : ℚ) + (deriv n : ℚ) - 2 * n

/-- A345048(n) = A342001(n) * A051709(n). -/
def a345048 (n : ℕ) : ℚ := a342001 n * a051709 n

/-- A345049(n) = A173557(n) * A345001(n). -/
def a345049 (n : ℕ) : ℚ := (a173557 n : ℚ) * a345001 n

/-- A345051: the numbers k >= 1 with A345048(k) = A345049(k). -/
def A345051 : Set ℕ := {k | 0 < k ∧ a345048 k = a345049 k}

/-- A000396: the perfect numbers, the k >= 1 equal to the sum of their proper divisors. -/
def A000396 : Set ℕ := {k | Nat.Perfect k}

/-- A166374: the numbers n >= 1 whose arithmetic derivative equals their Euler totient. -/
def A166374 : Set ℕ := {n | 0 < n ∧ deriv n = Nat.totient n}

/-- Karttunen's conjecture: A345051 is the disjoint union of A000396 and A166374. -/
theorem main : A345051 = A000396 ∪ A166374 ∧ Disjoint A000396 A166374 := by
  sorry

end OMA.S_oeis_a345051
