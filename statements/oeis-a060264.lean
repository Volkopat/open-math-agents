import Mathlib

/-!
# OEIS A060264: the first prime after 2n and distinct squares mod p

Source: https://oeis.org/A060264 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-fable-5-2), submitted by @jleguina.

Entry: First prime after 2n, offset 0 (2, 3, 5, 7, 11, 11, 13, 17, ...). Comment (Charles R
Greathouse IV, Dec 03 2022): Conjecture: for n > 2, this is the least prime p such that 1^2, 2^2,
3^2, ..., n^2 are distinct mod p. Checked to 10^4.

Formalization notes:
* The first prime after m is the least prime p with p > m, written as the least prime p >= m + 1.
* The squares 1^2, ..., n^2 are distinct mod p when i -> i^2 mod p is injective on {1, ..., n}.
* Controls: the definition gives 2, 3, 5, 7, 11, 11, 13, 17 for n = 0..7, as in the entry.
-/

namespace OMA.S_oeis_a060264

/-- The first prime after m. -/
def firstPrimeAfter (m : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (m + 1))

/-- A060264(n): the first prime after 2n. -/
def a (n : ℕ) : ℕ := firstPrimeAfter (2 * n)

/-- Greathouse's conjecture: for n > 2, a(n) is the least prime p such that 1^2, ..., n^2 are
distinct mod p. -/
theorem main : ∀ n : ℕ, 2 < n →
    IsLeast {p : ℕ | p.Prime ∧ Set.InjOn (fun i : ℕ => i ^ 2 % p) (Set.Icc 1 n)} (a n) := by
  sorry

end OMA.S_oeis_a060264
