import Mathlib

/-!
# A308107: Barker's recurrence

Source: https://oeis.org/A308107
Credit: @ivillar

Wesley Ivan Hurt's sequence: the sum of the smallest side lengths of all integer-sided scalene
triangles with perimeter n (offset 1; data 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 3, 5, 3, 9, ...), with
the entry's formula a(n) = Sum_{k=1..floor((n-1)/3)} Sum_{i=k+1..floor((n-k-1)/2)}
sign(floor((i+k)/(n-i-k+1))) * k. Colin Barker conjectured (May 13 2019)
a(n) = -a(n-1) + 2*a(n-3) + 4*a(n-4) + 2*a(n-5) - a(n-6) - 5*a(n-7) - 5*a(n-8) - a(n-9)
  + 2*a(n-10) + 4*a(n-11) + 2*a(n-12) - a(n-14) - a(n-15) for n > 15.

Status: conjecture recorded in the entry (Colin Barker, May 13 2019).

Formalization notes:
* The sum runs over all triples k + i + (n - i - k) = n with 1 <= k <= i <= n - i - k (the
  partitions of n into 3 parts) and adds the smallest side k exactly for the scalene triangles,
  k < i < n - i - k < i + k. This is the entry's double sum: its ranges k <= floor((n-1)/3),
  i in [k+1, floor((n-k-1)/2)] are the strict inequalities k < i < n - i - k, and
  sign(floor((i+k)/(n-i-k+1))) is 1 exactly when n - i - k < i + k and 0 otherwise.
* The recurrence is stated over ℤ; `a 0 = 0` (empty sum) is the value at n = 0.
* Barker's generating function
  x^9*(2 + 2*x + 2*x^2 + x^3) / ((1 - x)^4*(1 + x)^3*(1 + x^2)^2*(1 + x + x^2)^2)
  is the rational function determined by this recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a308107

/-- A308107: the sum of the smallest sides `k` of the scalene triangles `(k, i, n - i - k)`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (n / 3), ∑ i ∈ Finset.Icc k ((n - k) / 2),
    (if k < i ∧ i < n - i - k ∧ n - i - k < i + k then k else 0)

/-- Barker's conjectured recurrence for A308107, for every `n > 15`. -/
theorem main : ∀ n : ℕ, 15 < n →
    (a n : ℤ) = -a (n - 1) + 2 * a (n - 3) + 4 * a (n - 4) + 2 * a (n - 5) - a (n - 6) -
      5 * a (n - 7) - 5 * a (n - 8) - a (n - 9) + 2 * a (n - 10) + 4 * a (n - 11) +
      2 * a (n - 12) - a (n - 14) - a (n - 15) := by
  sorry

end OMA.S_oeis_a308107
