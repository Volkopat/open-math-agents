import Mathlib

/-!
# A092960: Least square of the form 'sum of n successive terms of a geometric progression + 1', or 0 if no such square exists.

Source: https://oeis.org/A092960
Credit: @agchua

Comment of A092960 (unsigned; the entry is by Amarnath Murthy, Mar 25 2004), verbatim:
  Conjecture: No term is zero.
The entry itself already settles this claim: Ray G. Opao (Feb 25 2005) notes that a(n) = 2^n for
even n (1 + 2 + ... + 2^(n-1) + 1 = 2^n), and Lien-Hung Su (Oct 03 2026) notes that for odd n >= 3
the progression (2^n - 3), 2*(2^n - 3), ..., 2^(n-1)*(2^n - 3) has sum (2^n - 3)*(2^n - 1), whose
successor is the square (2^n - 2)^2.

Formalisation. Offset 1. A geometric progression here has a first term x >= 1 and an integer
ratio r >= 2. The data exclude ratio 1 (a(3) = 36 = 5 + 10 + 20 + 1, although 1 + 1 + 1 + 1 = 4),
and with this reading the listed terms a(2), ..., a(13) are recomputed exactly. Since a(n) = 0
exactly when no such square exists, the conjecture says: for every n >= 1 there are x >= 1,
r >= 2 and m with x + x*r + ... + x*r^(n-1) + 1 = m^2. Admitting more progressions (for example
rational ratios) only weakens this claim. The listed value a(1) = 1 belongs to the one-term
progression 0; for n = 1 the claim holds under either reading.
-/

namespace OMA.S_oeis_a092960

/-- The sum of n successive terms x, x*r, ..., x*r^(n-1) of a geometric progression, plus 1. -/
def gpSumPlusOne (n x r : ℕ) : ℕ := (∑ i ∈ Finset.range n, x * r ^ i) + 1

/-- No term is zero: for every n >= 1 some such sum plus 1 is a square. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ x r m : ℕ, 1 ≤ x ∧ 2 ≤ r ∧ gpSumPlusOne n x r = m ^ 2 := by
  sorry

end OMA.S_oeis_a092960
