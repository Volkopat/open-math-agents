import Mathlib

/-!
# OEIS A345003: the sequence is the disjoint union of A000396 and A301939

Source: https://oeis.org/A345003 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Antti Karttunen, Jun 05 2021), offset 1: Numbers k for which A344998(k) = A344999(k).
Comment: Conjecture: Sequence is a disjoint union of A000396 and A301939.

The sequences involved, from their entries: A344998(n) = A342001(n) * A344753(n);
A344999(n) = A048250(n) * A345001(n); A342001(n) is the arithmetic derivative of n divided by
A003557(n); A003557(n) is n divided by the largest squarefree divisor of n; A344753(n) =
sigma(n) + psi(n) - 2n; A048250(n) is the sum of the squarefree divisors of n; A345001(n) =
sigma(n) + n' - 2n; n' = A003415(n) is the arithmetic derivative; psi = A001615 is the Dedekind
psi function n * Product_{p | n, p prime} (1 + 1/p); sigma = A000203 is the sum of divisors.
A000396 lists the perfect numbers, k equal to the sum of the proper divisors of k. A301939 lists
the integers whose arithmetic derivative is equal to their Dedekind function (offset 1, data
8, 81, 108, ...).

Formalization notes:
* n' is written in its closed form n * Sum_{p | n} v_p(n)/p (A003415, formula section) as
  Sum_{p | n} v_p(n) * (n / p), each division exact; it gives 0' = 1' = 0, p' = 1 for primes.
* The largest squarefree divisor of n is the product of the primes dividing n (A007947).
* A342001, psi, A344753, A345001, A344998 and A344999 are rational-valued, so that every
  division in the entries is exact and A345001 may be negative (A345001(1) = -1, as in its
  data); on n >= 1 they take the integer values listed in the entries.
* A345003 and A301939 are subsets of the positive integers (offset 1); perfect numbers are
  Mathlib's `Nat.Perfect` (sum of proper divisors equals n, and n > 0).
* `main` is the conjecture: A345003 = A000396 union A301939, and A000396, A301939 are disjoint.
* Controls proved in the proof file: 6, 8 are in A345003 and 1 is not; 8' = psi(8) = 12.
-/

namespace OMA.S_oeis_a345003

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

/-- psi(n) = A001615(n), the Dedekind psi function n * Product_{p | n} (1 + 1/p). -/
def psi (n : ℕ) : ℚ := (n : ℚ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ))

/-- A048250(n), the sum of the squarefree divisors of n. -/
def a048250 (n : ℕ) : ℕ := ∑ d ∈ n.divisors with Squarefree d, d

/-- A344753(n) = sigma(n) + psi(n) - 2n. -/
def a344753 (n : ℕ) : ℚ := (sigma n : ℚ) + psi n - 2 * n

/-- A345001(n) = sigma(n) + n' - 2n. -/
def a345001 (n : ℕ) : ℚ := (sigma n : ℚ) + (deriv n : ℚ) - 2 * n

/-- A344998(n) = A342001(n) * A344753(n). -/
def a344998 (n : ℕ) : ℚ := a342001 n * a344753 n

/-- A344999(n) = A048250(n) * A345001(n). -/
def a344999 (n : ℕ) : ℚ := (a048250 n : ℚ) * a345001 n

/-- A345003: the numbers k >= 1 with A344998(k) = A344999(k). -/
def A345003 : Set ℕ := {k | 0 < k ∧ a344998 k = a344999 k}

/-- A000396: the perfect numbers, the k >= 1 equal to the sum of their proper divisors. -/
def A000396 : Set ℕ := {k | Nat.Perfect k}

/-- A301939: the integers n >= 1 whose arithmetic derivative equals their Dedekind psi. -/
def A301939 : Set ℕ := {n | 0 < n ∧ (deriv n : ℚ) = psi n}

/-- Karttunen's conjecture: A345003 is the disjoint union of A000396 and A301939. -/
theorem main : A345003 = A000396 ∪ A301939 ∧ Disjoint A000396 A301939 := by
  sorry

end OMA.S_oeis_a345003
