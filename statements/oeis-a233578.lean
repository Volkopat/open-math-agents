import Mathlib

/-!
# OEIS A233578: Kaarhus's conjecture on Bernoulli numerators congruent to 1 mod 6

Source: https://oeis.org/A233578 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Michael G. Kaarhus, Dec 13 2013), offset 1: n >= 2 such that the denominator/6 of
Bernoulli(n) is congruent to {1, 5, 7, 13 or 19} modulo 30. Comment: Conjecture: for these and
only these n, the absolute value of the numerator of Bernoulli(n) is congruent 1 modulo 6. If my
conjecture is true, then you can obtain the residue modulo 6 of the abs. value of Bernoulli
numerators by calculating their denominators/6 modulo 30. Program uses the von Staudt-Clausen
Theorem. None of these n are in the complementary sequence, A233579 (n such that the
denominator/6 of Bernoulli(n) is congruent to {11, 17, 23, 25 or 29} modulo 30). I have checked
and verified that, up to n = 50446, the union of A233578 and A233579 is all even numbers >= 2.

Formalization notes:
* Bernoulli(n) is Mathlib's `bernoulli n` (its value at n = 1 plays no role, since n >= 2), and
  numerator and denominator are those of the fraction in lowest terms.
* n is a term when n >= 2, 6 divides the denominator of Bernoulli(n), and the quotient is
  congruent to 1, 5, 7, 13 or 19 modulo 30.
* `main` is the conjecture of the comment, for every n >= 2. The other sentences are not further
  conjectures: one draws a consequence, the disjointness from A233579 holds because the two sets
  of residues are disjoint, and the last one reports a finite check.
* Controls: the denominator of Bernoulli(100) is 33330, as in the entry's example.
-/

namespace OMA.S_oeis_a233578

/-- Membership in A233578. -/
def InSeq (n : ℕ) : Prop :=
  2 ≤ n ∧ 6 ∣ (bernoulli n).den ∧ (bernoulli n).den / 6 % 30 ∈ ({1, 5, 7, 13, 19} : Finset ℕ)

/-- Kaarhus's conjecture: for n >= 2, n is a term iff |numerator of Bernoulli(n)| = 1 mod 6. -/
theorem main : ∀ n : ℕ, 2 ≤ n → (InSeq n ↔ (bernoulli n).num.natAbs % 6 = 1) := by
  sorry

end OMA.S_oeis_a233578
