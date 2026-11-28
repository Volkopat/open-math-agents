import Mathlib

/-!
# OEIS A342039: a(n) >= prime(n) - 1 for all n

Source: https://oeis.org/A342039 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Jianing Song, Feb 26 2021), offset 1: a(n) is the index of the first occurrence of the
term in A307437 that is divisible by p and greater than p, p = prime(n).
A307437 (offset 1): a(n) is the smallest k such that 2n divides psi(k), psi = A002322.
A002322 is the Carmichael function lambda(k), the exponent of the multiplicative group mod k.
Comment: Conjecture: a(n) >= prime(n)-1 for all n.

Formalization notes:
* lambda is Mathlib's `ArithmeticFunction.carmichael`, the exponent of `(ZMod k)ˣ`.
* `IsA307437 m k` says that k = A307437(m): k is positive, 2m divides lambda(k), and no smaller
  positive j has 2m dividing lambda(j).
* a(n) is the least m >= 1 such that A307437(m) is divisible by p = prime(n) and greater than p.
  So a(n) >= p - 1 for every n says exactly: for every prime p and every m >= 1, if A307437(m)
  is a multiple of p greater than p, then m >= p - 1. That is `main` (it does not need the
  existence of a(n), which the entry proves).
-/

namespace OMA.S_oeis_a342039

open ArithmeticFunction

/-- k = A307437(m): k is the least positive integer with 2m dividing lambda(k). -/
def IsA307437 (m k : ℕ) : Prop :=
  0 < k ∧ 2 * m ∣ carmichael k ∧ ∀ j, 0 < j → j < k → ¬ 2 * m ∣ carmichael j

/-- Song's conjecture: a(n) >= prime(n) - 1, i.e. whenever A307437(m) is a multiple of the prime
p greater than p, m >= p - 1. -/
theorem main : ∀ p m k : ℕ, p.Prime → 1 ≤ m → IsA307437 m k → p ∣ k → p < k → p - 1 ≤ m := by
  sorry

end OMA.S_oeis_a342039
