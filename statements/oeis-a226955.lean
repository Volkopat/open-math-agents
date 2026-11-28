import Mathlib

/-!
# A226955: Number of representations of n! as a sum of 3 positive cubes.

Source: https://oeis.org/A226955
Credit: @darealpandaboi

Conjecture (Altug Alkan, Aug 16 2020): for any t >= 0, there are only finitely many values of n
such that a(n) = t.

Translation notes.
* Representations are unordered: a(n) counts triples 1 <= x <= y <= z with
  x^3 + y^3 + z^3 = n!. This reproduces the listed data 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 4, 0
  for n = 1..13 (checked by computer); counting ordered triples would give 6 for n = 9.
* The offset is 1, so n ranges over positive integers.
-/

namespace OMA.S_oeis_a226955

/-- The number of triples 1 <= x <= y <= z with x^3 + y^3 + z^3 = n!. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n.factorial ×ˢ Finset.Icc 1 n.factorial ×ˢ Finset.Icc 1 n.factorial).filter
    (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
      t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3 = n.factorial)).card

theorem main : ∀ t : ℕ, {n : ℕ | 0 < n ∧ a n = t}.Finite := by
  sorry

end OMA.S_oeis_a226955
