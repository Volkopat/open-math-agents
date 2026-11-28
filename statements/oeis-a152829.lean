import Mathlib

/-!
# A152829: Numbers k whose squares can be written in exactly one way as a sum of three squares: k^2 = a^2 + b^2 + c^2 with 1 <= a <= b <= c.

Source: https://oeis.org/A152829
Credit: @darealpandaboi

Conjectures: 3, 7 and 13 are the only odd terms (equivalent, since 2k is a term iff k is, to
Colin Barker's conjecture); and a(n) = 2*a(n-3) for n > 5.

Translation notes.
* r(n) counts triples 1 <= a <= b <= c with a^2 + b^2 + c^2 = n; k is a term when r(k^2) = 1.
* The data begin 3, 6, 7, 12, 13, 14, so a(n) = 2*a(n-3) for n > 5 says exactly that the terms
  are 3, 6, 7 and 12*2^j, 13*2^j, 14*2^j for j >= 0 (these are in increasing order as listed,
  since 14*2^j < 12*2^(j+1)). Both conjectures are stated: the odd terms are 3, 7, 13, and the
  set of terms is the set just described.
* This reproduces the listed data, and for k < 1600 the terms are exactly as described
  (checked by computer).
-/

namespace OMA.S_oeis_a152829

/-- The number of triples 1 <= a <= b <= c with a^2 + b^2 + c^2 = n. -/
def r (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = n)).card

theorem main :
    {k : ℕ | r (k ^ 2) = 1 ∧ Odd k} = {3, 7, 13} ∧
    {k : ℕ | r (k ^ 2) = 1} =
      {3, 6, 7} ∪ {k : ℕ | ∃ c j : ℕ, (c = 12 ∨ c = 13 ∨ c = 14) ∧ k = c * 2 ^ j} := by
  sorry

end OMA.S_oeis_a152829
