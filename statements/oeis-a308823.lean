import Mathlib

/-!
# A308823: Barker's recurrence

Source: https://oeis.org/A308823
Credit: @ivillar

Wesley Ivan Hurt's sequence: the sum of the smallest parts in the partitions of n into 5 parts
(offset 0; data 0, 0, 0, 0, 0, 1, 1, 2, 3, 5, 8, 11, ...), with the entry's formula
a(n) = Sum_{l=1..floor(n/5)} Sum_{k=l..floor((n-l)/4)} Sum_{j=k..floor((n-k-l)/3)}
  Sum_{i=j..floor((n-j-k-l)/2)} l.
Colin Barker conjectured (Jun 30 2019)
a(n) = a(n-1) + a(n-2) - 2*a(n-6) - 2*a(n-7) + a(n-8) + a(n-9) + 2*a(n-10) + a(n-11) + a(n-12) -
  2*a(n-13) - 2*a(n-14) + a(n-18) + a(n-19) - a(n-20) for n > 19.

Status: conjecture recorded in the entry (Colin Barker, Jun 30 2019).

Formalization notes:
* The quadruple sum is the entry's formula; it enumerates the partitions
  l + k + j + i + (n - i - j - k - l) of n with 1 <= l <= k <= j <= i <= n - i - j - k - l, and the
  summand is the smallest part `l`.
* The recurrence is stated over ℤ.
* Barker's generating function
  x^5 /
  ((1 - x)^6*(1 + x)^2*(1 + x^2)*(1 + x + x^2)*(1 + x + x^2 + x^3 + x^4)^2)
  is the rational function determined by this recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a308823

/-- A308823: the entry's quadruple sum over the partitions of `n` into 5 parts. -/
def a (n : ℕ) : ℕ :=
  ∑ l ∈ Finset.Icc 1 (n / 5), ∑ k ∈ Finset.Icc l ((n - l) / 4),
    ∑ j ∈ Finset.Icc k ((n - k - l) / 3), ∑ i ∈ Finset.Icc j ((n - j - k - l) / 2), l

/-- Barker's conjectured recurrence for A308823, for every `n > 19`. -/
theorem main : ∀ n : ℕ, 19 < n →
    (a n : ℤ) = a (n - 1) + a (n - 2) - 2 * a (n - 6) - 2 * a (n - 7) + a (n - 8) + a (n - 9)
      + 2 * a (n - 10) + a (n - 11) + a (n - 12) - 2 * a (n - 13) - 2 * a (n - 14) + a (n - 18)
      + a (n - 19) - a (n - 20) := by
  sorry

end OMA.S_oeis_a308823
