import Mathlib

/-!
# A337484: Number of ordered triples of positive integers summing to n that are neither strictly increasing nor strictly decreasing.

Source: https://oeis.org/A337484
Credit: @agchua

Colin Barker (Sep 13 2020), in the formula section of A337484:
  Conjectures from Colin Barker, Sep 13 2020: (Start)
  G.f.: x^3*(1 + 2*x + 2*x^2 - x^3) / ((1 - x)^3*(1 + x)*(1 + x + x^2)).
  a(n) = a(n-1) + a(n-2) - a(n-4) - a(n-5) + a(n-6) for n>6.
  (End)
This file states the recurrence, for n > 6 exactly as written. (The g.f. has denominator
(1-x)^3 (1+x) (1+x+x^2) = 1 - x - x^2 + x^4 + x^5 - x^6 and a numerator of degree 6, so it is the
same recurrence together with the listed initial terms a(0), ..., a(6); it is not restated here.)
The sequence has offset 0. A triple (x, y, z) of positive integers with x + y + z = n has all
entries in {1, ..., n}; strictly increasing means x < y < z and strictly decreasing x > y > z, as
in the entry's Mathematica program (Less and Greater). Terms are taken in ℤ.
-/

namespace OMA.S_oeis_a337484

/-- A337484(n): the ordered triples (x, y, z) of positive integers with x + y + z = n that are
neither strictly increasing nor strictly decreasing. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = n ∧ ¬ (t.1 < t.2.1 ∧ t.2.1 < t.2.2) ∧
      ¬ (t.1 > t.2.1 ∧ t.2.1 > t.2.2))).card

/-- Barker's conjecture: a(n) = a(n-1) + a(n-2) - a(n-4) - a(n-5) + a(n-6) for n > 6. -/
theorem main : ∀ n : ℕ, 6 < n →
    (a n : ℤ) = (a (n - 1) : ℤ) + (a (n - 2) : ℤ) - (a (n - 4) : ℤ) - (a (n - 5) : ℤ)
      + (a (n - 6) : ℤ) := by
  sorry

end OMA.S_oeis_a337484
