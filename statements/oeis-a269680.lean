import Mathlib

/-!
# A269680: Number of length-5 0..n arrays with no repeated value differing from the previous repeated value by other than plus or minus one modulo n+1.

Source: https://oeis.org/A269680
Credit: @agchua

Colin Barker (Jan 26 2019), in the formula section of A269680:
  Conjectures from Colin Barker, Jan 26 2019: (Start)
  G.f.: 2*x*(7 + 45*x - 7*x^2 + 40*x^3 - 36*x^4 + 13*x^5 - 2*x^6) / (1 - x)^6.
  a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>7.
  (End)
This file states both parts: the recurrence for n > 7 (offset 1, so all indices are terms), and
the g.f. as an identity of formal power series over Q. The offset is 1, so the g.f. is the
series sum over n >= 1 of a(n) x^n, written as X * mk (fun n => a (n + 1)) (the definition
below also has a value at n = 0, which the g.f. does not concern):
X * (sum of a(n+1) X^n) * (1 - X)^6 = 2X(7 + 45X - 7X^2 + 40X^3 - 36X^4 + 13X^5 - 2X^6).
Definition (R. H. Hardin's convention for these arrays): an array is (x1, ..., x5) with entries
in 0..n. A repeated value is an entry x(i) with x(i) = x(i+1), i = 1..4, taken in the order of
i; the previous repeated value of the one at i is the one at the largest j < i with
x(j) = x(j+1). The condition is that no repeated value differs from its previous repeated value
by anything other than plus or minus one modulo n+1, i.e. R n x(j) x(i) below holds for every
pair (j, i) of consecutive repetitions. The six implications of ok are the six possible such
pairs: (1,2), (2,3), (3,4), then (1,3) with no repetition at 2, (2,4) with none at 3, and (1,4)
with none at 2 and 3. The definition gives the listed terms 14, 174, 820, 2670, 6918, 15358
for n = 1..6 (checked by direct enumeration).
-/

namespace OMA.S_oeis_a269680

/-- v differs from u by plus or minus one modulo n + 1. -/
def R (n u v : ℕ) : Prop := v ≡ u + 1 [MOD n + 1] ∨ v + 1 ≡ u [MOD n + 1]
instance (n u v : ℕ) : Decidable (R n u v) := by
  unfold R
  exact instDecidableOr

/-- The condition on the array (x1, ..., x5): every repeated value that has a previous repeated
value differs from it by plus or minus one modulo n + 1. -/
def ok (n x1 x2 x3 x4 x5 : ℕ) : Prop :=
  ((x1 = x2 → x2 = x3 → R n x1 x2) ∧ (x2 = x3 → x3 = x4 → R n x2 x3) ∧
    (x3 = x4 → x4 = x5 → R n x3 x4)) ∧
  ((x1 = x2 → x2 ≠ x3 → x3 = x4 → R n x1 x3) ∧ (x2 = x3 → x3 ≠ x4 → x4 = x5 → R n x2 x4) ∧
    (x1 = x2 → x2 ≠ x3 → x3 ≠ x4 → x4 = x5 → R n x1 x4))
instance (n x1 x2 x3 x4 x5 : ℕ) : Decidable (ok n x1 x2 x3 x4 x5) := by
  unfold ok
  exact instDecidableAnd

/-- A269680: the number of arrays (x1, ..., x5) with entries in 0..n satisfying ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t : ℕ × ℕ × ℕ × ℕ × ℕ => ok n t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2)).card

/-- Barker's conjectures: a(n) = 6a(n-1) - 15a(n-2) + 20a(n-3) - 15a(n-4) + 6a(n-5) - a(n-6)
for n > 7, and the g.f. 2x(7 + 45x - 7x^2 + 40x^3 - 36x^4 + 13x^5 - 2x^6)/(1 - x)^6. -/
theorem main : (∀ n : ℕ, 8 ≤ n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
        6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - PowerSeries.X) ^ 6 =
      2 * PowerSeries.X * (7 + 45 * PowerSeries.X - 7 * PowerSeries.X ^ 2 +
        40 * PowerSeries.X ^ 3 - 36 * PowerSeries.X ^ 4 + 13 * PowerSeries.X ^ 5 -
        2 * PowerSeries.X ^ 6) := by
  sorry

end OMA.S_oeis_a269680
