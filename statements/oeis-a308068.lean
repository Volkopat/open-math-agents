import Mathlib

/-!
# A308068: Barker's recurrence

Source: https://oeis.org/A308068
Credit: @ivillar

Wesley Ivan Hurt's sequence: the number of integer-sided triangles with perimeter n whose longest
side length is even (data 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, ...; offset 1), with the entry's formula
a(n) = Sum_{k=1..floor(n/3)} Sum_{i=k..floor((n-k)/2)}
  sign(floor((i+k)/(n-i-k+1))) * ((n-i-k-1) mod 2).
Colin Barker conjectured (May 11 2019)
a(n) = a(n-1) - a(n-2) + a(n-3) + a(n-4) - a(n-5) + 2*a(n-6) - 2*a(n-7) + a(n-8) - a(n-9)
  - a(n-10) + a(n-11) - a(n-12) + a(n-13) for n > 13.

Status: conjecture recorded in the entry (Colin Barker, May 11 2019).

Formalization notes:
* The double sum enumerates the triples k + i + (n - i - k) = n with 1 <= k <= i <= n - i - k;
  sign(floor((i+k)/(n-i-k+1))) is 1 exactly when n - i - k < i + k (the triangle inequality) and
  0 otherwise, which is written as an `if`; as the longest side `n - i - k` is at least 1,
  `(n - i - k - 1) % 2` is 1 exactly when it is even.
* The recurrence is stated over ℤ; `a 0 = 0` (empty sum) is the value at n = 0.
* Barker's generating function
  x^5 /
  ((1 - x)^3*(1 + x)^2*(1 - x + x^2)*(1 + x^2)^2*(1 + x + x^2))
  is the rational function determined by this recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a308068

/-- A308068: the entry's double sum over the triangles `(k, i, n - i - k)` with perimeter `n`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (n / 3), ∑ i ∈ Finset.Icc k ((n - k) / 2),
    (if n - i - k < i + k then (n - i - k - 1) % 2 else 0)

/-- Barker's recurrence for A308068, for every `n > 13`. -/
theorem main : ∀ n : ℕ, 13 < n →
    (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 4) - a (n - 5) + 2 * a (n - 6) -
      2 * a (n - 7) + a (n - 8) - a (n - 9) - a (n - 10) + a (n - 11) - a (n - 12) +
      a (n - 13) := by
  sorry

end OMA.S_oeis_a308068
