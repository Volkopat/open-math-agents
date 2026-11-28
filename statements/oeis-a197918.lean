import Mathlib

/-!
# OEIS A197918: the terms other than 2, 5, 17 satisfy p XOR 22 = p + 22

Source: https://oeis.org/A197918 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Brad Clardy, Oct 24 2011), offset 1: Pythagorean primes p such that for all primes q < p,
p XOR q is not equal to p - q. Comment: It is conjectured that with the exception of the first
three terms (2,5,17) all of the terms are a subset of all primes p such that p XOR 22 = p + 22.

Formalization notes:
* The listed terms begin with 2, and the entry's PARI program admits every prime except those
  congruent to 3 mod 4; so the Pythagorean primes are read as 2 and the primes congruent to 1 mod 4
  (the primes that are sums of two squares). The conjecture excludes 2 anyway.
* XOR is bitwise exclusive or on natural numbers (`^^^`).
* The conjecture says that every term p other than 2, 5 and 17 satisfies p XOR 22 = p + 22.
* Controls (checked by kernel decide in a scratch copy of the proof file, with the definition
  below): the terms below 300 are 2, 5, 17, 41, 73, 97, 137, 193, 257, as in the entry.
-/

namespace OMA.S_oeis_a197918

/-- Membership in A197918. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ (p = 2 ∨ p % 4 = 1) ∧ ∀ q : ℕ, q.Prime → q < p → p ^^^ q ≠ p - q

/-- Clardy's conjecture: every term other than 2, 5, 17 satisfies p XOR 22 = p + 22. -/
theorem main : ∀ p : ℕ, IsTerm p → p ≠ 2 → p ≠ 5 → p ≠ 17 → p ^^^ 22 = p + 22 := by
  sorry

end OMA.S_oeis_a197918
