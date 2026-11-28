import Mathlib

/-!
# A302393: Barker's recurrence

Source: https://oeis.org/A302393
Credit: @ivillar

Wesley Ivan Hurt's sequence: the number of even parts in the partitions of 3n into 3 parts
(offset 1; data 0, 5, 8, 18, 24, 41, 50, 72, 84, 113, ...; Mathematica
Table[Count[Flatten[IntegerPartitions[3 n, {3}]], _?EvenQ], {n, 100}]). Colin Barker conjectured
(Apr 07 2018) a(n) = a(n-1) + a(n-2) - a(n-3) + a(n-4) - a(n-5) - a(n-6) + a(n-7) for n > 7.

Status: conjecture recorded in the entry (Colin Barker, Apr 07 2018).

Formalization notes:
* The partitions of 3n into 3 parts are enumerated as k + i + (3n - i - k) with
  1 <= k <= i <= 3n - i - k, i.e. k in [1, n] and i in [k, floor((3n - k)/2)].
* `(x + 1) % 2` is 1 when the part `x` is even and 0 otherwise, so the summand counts the even parts
  of the partition (with multiplicity, as Count[Flatten[...]] does).
* The recurrence is stated over ℤ; `a 0 = 0` is the empty sum and is not used for n > 7.
* Barker's generating function
  x^2*(5 + 3*x + 5*x^2 + 3*x^3 + 2*x^4) / ((1 - x)^3*(1 + x)^2*(1 + x^2))
  is the rational function determined by this recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a302393

/-- A302393: the number of even parts, counted with multiplicity, over all partitions
`k + i + (3n - i - k)` of `3n` with `1 ≤ k ≤ i ≤ 3n - i - k`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc k ((3 * n - k) / 2),
    ((k + 1) % 2 + (i + 1) % 2 + (3 * n - i - k + 1) % 2)

/-- Barker's conjectured recurrence for A302393, for every `n > 7`. -/
theorem main : ∀ n : ℕ, 7 < n →
    (a n : ℤ) = a (n - 1) + a (n - 2) - a (n - 3) + a (n - 4) - a (n - 5) - a (n - 6) +
      a (n - 7) := by
  sorry

end OMA.S_oeis_a302393
