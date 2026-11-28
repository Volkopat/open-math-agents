import Mathlib

/-!
# A136404: Square numbers with more divisors than any smaller square number.

Source: https://oeis.org/A136404
Credit: @agchua

Comment of A136404 (unsigned; the entry is by J. Lowell, Mar 30 2008):
  Conjecture: square roots of the terms of this sequence are the same terms as A126098.
A126098 (offset 1): Where records occur in A018892. A018892 (offset 1): Number of ways to write
1/n as a sum of exactly 2 unit fractions, that is, the number of pairs x <= y of positive
integers with 1/n = 1/x + 1/y.
Offsets and ranges: A136404 has offset 1 and a(1) = 1, so its terms are positive squares, each
with more divisors than every smaller positive square. A record of A018892 occurs at n >= 1 when
A018892(k) < A018892(n) for every k with 1 <= k < n (so n = 1 is a record, as in the data
1, 2, 4, 6, 12, ...). Every term of A136404 is a square, so the conjecture says: for every m,
m^2 is a term of A136404 if and only if m is a term of A126098.
A later comment of A136404 (R. J. Mathar, Apr 04 2008) says that the terms are the squares of
the indices of the records of A048691 (the number of divisors of n^2).
-/

namespace OMA.S_oeis_a136404

/-- s is a term of A136404: a positive square with more divisors than every smaller positive
square. -/
def IsTermA136404 (s : ℕ) : Prop :=
  0 < s ∧ IsSquare s ∧ ∀ t : ℕ, 0 < t → t < s → IsSquare t → t.divisors.card < s.divisors.card

/-- A018892(n): the number of pairs (x, y) of positive integers with x <= y and
1/n = 1/x + 1/y. -/
noncomputable def A018892 (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | 0 < p.1 ∧ p.1 ≤ p.2 ∧ (1 : ℚ) / n = 1 / p.1 + 1 / p.2}

/-- n is a term of A126098: n >= 1 and A018892(n) is larger than every earlier value. -/
noncomputable def IsTermA126098 (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ k : ℕ, 1 ≤ k → k < n → A018892 k < A018892 n

/-- The conjecture: the square roots of the terms of A136404 are the terms of A126098. -/
theorem main : ∀ m : ℕ, IsTermA136404 (m ^ 2) ↔ IsTermA126098 m := by
  sorry

end OMA.S_oeis_a136404
