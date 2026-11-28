import Mathlib

/-!
# OEIS A233579: Kaarhus's conjecture on Bernoulli numerators congruent to 5 mod 6

Source: https://oeis.org/A233579 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Michael G. Kaarhus, Dec 13 2013), offset 1: Numbers n such that the denominator/6 of
Bernoulli(n) is congruent to {11, 17, 23, 25 or 29} modulo 30. Comment: Conjecture: for these and
only these n, the absolute value of the numerator of Bernoulli(n) is congruent 5 modulo 6. If this
is true, then you can obtain the residue modulo 6 of the absolute value of Bernoulli numerators by
calculating their denominators/6 modulo 30. The program uses the von Staudt-Clausen Theorem. None
of these n are in the complementary sequence, A233578 (n >= 2 such that the denominator/6 of
Bernoulli_n is congruent to {1, 5, 7, 13 or 19} modulo 30). I have checked and verified that, up
to n = 50446, the union of A233578 and A233579 is all even numbers >= 2.

Formalization notes:
* Bernoulli(n) is Mathlib's `bernoulli n` (with B_1 = -1/2), and numerator and denominator are
  those of the fraction in lowest terms.
* denominator/6 is natural-number division. The denominator is divisible by 6 for even n >= 2
  (von Staudt-Clausen) and is 1 or 2 for the other n; there the quotient is 0, which is not one
  of the residues, so those n are not terms, as in the entry.
* `main` is the conjecture of the comment, for every n >= 0. The other sentences are not further
  conjectures: one draws a consequence, the disjointness from A233578 holds because the two sets
  of residues are disjoint, and the last one reports a finite check.
* Controls (checked by kernel decide in a scratch copy of the proof file, through its
  von Staudt-Clausen lemma): the denominator of Bernoulli(112) is 1671270, as in the entry's
  example.
-/

namespace OMA.S_oeis_a233579

/-- Kaarhus's conjecture: n is a term iff |numerator of Bernoulli(n)| = 5 mod 6. -/
theorem main :
    ∀ n : ℕ, ((bernoulli n).den / 6 % 30 ∈ ({11, 17, 23, 25, 29} : Finset ℕ) ↔
      (bernoulli n).num.natAbs % 6 = 5) := by
  sorry

end OMA.S_oeis_a233579
