import Mathlib

/-!
# OEIS A332446: every prime congruent to 3 mod 8 is a term

Source: https://oeis.org/A332446 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Antti Karttunen, Feb 14 2020), offset 1: Numbers k for which A087808(sigma(k)) is equal to
A087808(2*k). Comment: Conjecture: includes all terms of A007520. - Bill McEachen, Dec 10 2023.
A007520: Primes == 3 (mod 8). A087808: a(0) = 0; a(2n) = 2a(n), a(2n+1) = a(n) + 1.

Formalization notes:
* A087808 is defined by the recursion of its entry, through n / 2.
* sigma(k) is the sum of the divisors of k, written as a sum over `Nat.divisors`.
* A term of A332446 is a positive k with A087808(sigma(k)) = A087808(2k), as the entry's PARI
  program tests.
* `main` says: every prime p with p mod 8 = 3 is a term.
* Controls from the entry (proved in the proof file by kernel computation): 3, 6 and 28 are terms,
  4 and 5 are not.
-/

namespace OMA.S_oeis_a332446

/-- A087808: a(0) = 0; a(2n) = 2a(n), a(2n+1) = a(n) + 1. -/
def A087808 (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else if n % 2 = 0 then 2 * A087808 (n / 2) else A087808 (n / 2) + 1
decreasing_by all_goals omega

/-- k is a term of A332446: A087808(sigma(k)) = A087808(2k), sigma(k) the sum of the divisors. -/
def InA332446 (k : ℕ) : Prop := 0 < k ∧ A087808 (∑ d ∈ k.divisors, d) = A087808 (2 * k)

/-- McEachen's conjecture: A332446 includes every term of A007520, the primes congruent to 3 mod 8. -/
theorem main : ∀ p : ℕ, p.Prime → p % 8 = 3 → InA332446 p := by
  sorry

end OMA.S_oeis_a332446
