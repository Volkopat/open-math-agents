import Mathlib

/-!
# A308066: Barker's recurrence

Source: https://oeis.org/A308066
Credit: @ivillar

Wesley Ivan Hurt's sequence: the number of triangles with perimeter n whose side lengths are all
even (offset 1; data 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 2, ...), with the entry's formula
a(n) = Sum_{k=1..floor(n/3)} Sum_{i=k..floor((n-k)/2)}
  sign(floor((i+k)/(n-i-k+1))) * ((i-1) mod 2) * ((k-1) mod 2) * ((n-i-k-1) mod 2).
Colin Barker conjectured (May 11 2019)
a(n) = a(n-4) + a(n-6) + a(n-8) - a(n-10) - a(n-12) - a(n-14) + a(n-18) for n > 18.

Status: known result; the entry records "The above conjectures are correct" and
a(n) = A005044(n/2) for even n, a(n) = 0 for odd n (Andrew Howroyd, Nov 06 2025).

Formalization notes:
* The double sum enumerates the triples k + i + (n - i - k) = n with 1 <= k <= i <= n - i - k.
  sign(floor((i+k)/(n-i-k+1))) is 1 exactly when n - i - k < i + k (the triangle inequality), and
  as every side is at least 1, ((i-1) mod 2)*((k-1) mod 2)*((n-i-k-1) mod 2) is 1 exactly when all
  three sides are even; the summand is written as the corresponding `if`.
* The recurrence is stated over ℤ; `a 0 = 0` (empty sum) is the value at n = 0.
* Barker's generating function
  x^6 / ((1 - x)^3*(1 + x)^3*(1 - x + x^2)*(1 + x^2)^2*(1 + x + x^2)*(1 + x^4))
  is the rational function determined by this recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a308066

/-- A308066: the number of triangles `(k, i, n - i - k)` with perimeter `n` and all sides even. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (n / 3), ∑ i ∈ Finset.Icc k ((n - k) / 2),
    (if k % 2 = 0 ∧ i % 2 = 0 ∧ (n - i - k) % 2 = 0 ∧ n - i - k < i + k then 1 else 0)

/-- Barker's recurrence for A308066 (now known to hold), for every `n > 18`. -/
theorem main : ∀ n : ℕ, 18 < n →
    (a n : ℤ) = a (n - 4) + a (n - 6) + a (n - 8) - a (n - 10) - a (n - 12) - a (n - 14) +
      a (n - 18) := by
  sorry

end OMA.S_oeis_a308066
