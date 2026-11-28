import Mathlib

/-!
# A247727: Number of length 1+3 0..n arrays with no disjoint pairs in any consecutive four terms having the same sum.

Source: https://oeis.org/A247727
Credit: @agchua

Formula section of A247727:
  Empirical: a(n) = n^4 + 2*n^3 + 3*n^2 + 2*n.
  Conjectures from Colin Barker, Nov 07 2018: (Start)
  G.f.: 8*x*(1 + x + x^2) / (1 - x)^5.
  a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5. (End)
  Conjectured e.g.f.: exp(x)*x*(8 + 16*x + 8*x^2 + x^3). - Stefano Spezia, Mar 12 2025
(The empirical formula is R. H. Hardin's, Sep 23 2014.) This file states all four: the closed form
for n ≥ 1 (offset 1), the recurrence for n > 5 as written, the g.f. as an identity of formal power
series over ℚ, (∑ a(n) X^n) * (1 - X)^5 = 8X(1 + X + X^2), and the e.g.f. as
∑ a(n) X^n / n! = exp(X) * X * (8 + 16X + 8X^2 + X^3). The series start at n = 0; the definition
gives a(0) = 0 (for n = 0 every pairing of the four entries has equal sums), so they agree with the
series of the entry, which start at n = 1.
An array (x1, x2, x3, x4) of length 1+3 = 4 with entries in 0..n has exactly one block of four
consecutive terms, and its pairs of disjoint pairs are the three pairings {x1,x2},{x3,x4};
{x1,x3},{x2,x4}; {x1,x4},{x2,x3}. The condition is that no pairing has equal sums. (This reading
reproduces the 37 listed terms.)
-/

namespace OMA.S_oeis_a247727

/-- A247727(n): the number of (x1, x2, x3, x4) in {0, ..., n}^4 with x1 + x2 ≠ x3 + x4,
x1 + x3 ≠ x2 + x4 and x1 + x4 ≠ x2 + x3. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n).filter
    (fun t : ℕ × ℕ × ℕ × ℕ => t.1 + t.2.1 ≠ t.2.2.1 + t.2.2.2 ∧
      t.1 + t.2.2.1 ≠ t.2.1 + t.2.2.2 ∧ t.1 + t.2.2.2 ≠ t.2.1 + t.2.2.1)).card

/-- The empirical closed form (n ≥ 1), Barker's recurrence (n > 5) and g.f., and Spezia's e.g.f. -/
theorem main : (∀ n : ℕ, 1 ≤ n → a n = n ^ 4 + 2 * n ^ 3 + 3 * n ^ 2 + 2 * n) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 10 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ)
        - 5 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 5 =
      8 * PowerSeries.X * (1 + PowerSeries.X + PowerSeries.X ^ 2) ∧
    PowerSeries.mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) =
      PowerSeries.exp ℚ * PowerSeries.X *
        (8 + 16 * PowerSeries.X + 8 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) := by
  sorry

end OMA.S_oeis_a247727
