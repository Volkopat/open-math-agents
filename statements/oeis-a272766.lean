import Mathlib

/-!
# OEIS A272766: every primorial number is a term

Source: https://oeis.org/A272766 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Juri-Stepan Gerasimov, May 06 2016), offset 1: Numbers n such that A281363(n) = n-1.
A281363 (same author, Apr 30 2016): Smallest m>0 such that (2*n)^2 - 1 divides (2^m)^(2*n) - 1.
Comment: Conjecture: primorial numbers (A002110) are terms of this sequence.

Formalization notes:
* `IsTerm n` says that n - 1 is positive and is the least positive m such that (2n)^2 - 1
  divides (2^m)^(2n) - 1, which is A281363(n) = n - 1. Natural-number subtraction is harmless
  here: (2n)^2 >= 4 and (2^m)^(2n) >= 1 for n >= 1.
* The primorial numbers A002110 are 1, 2, 6, 30, 210, 2310, ..., the products of the first k
  primes; Mathlib's `primorial n` is the product of the primes at most n, so these are exactly
  the values `primorial n`. The value 1 (k = 0) is excluded, since a(1) would need
  A281363(1) = 0 while A281363 is positive; the sequence starts at 2.
* Controls proved in the proof file: 2, 6 and 30 are terms.
-/

namespace OMA.S_oeis_a272766

/-- n is a term: n - 1 is positive and is the smallest positive m with
(2n)^2 - 1 dividing (2^m)^(2n) - 1, that is, A281363(n) = n - 1. -/
def IsTerm (n : ℕ) : Prop :=
  0 < n - 1 ∧ (2 * n) ^ 2 - 1 ∣ (2 ^ (n - 1)) ^ (2 * n) - 1 ∧
    ∀ m, 0 < m → m < n - 1 → ¬ ((2 * n) ^ 2 - 1 ∣ (2 ^ m) ^ (2 * n) - 1)

/-- Gerasimov's conjecture: every primorial number greater than 1 is a term. -/
theorem main : ∀ n : ℕ, 1 < primorial n → IsTerm (primorial n) := by
  sorry

end OMA.S_oeis_a272766
