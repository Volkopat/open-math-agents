import Mathlib

/-!
# A325691: Barker's recurrence

Source: https://oeis.org/A325691
Credit: @ivillar

Gus Wiseman's sequence: the number of length-3 integer partitions of n whose largest part is not
greater than the sum of the other two (offset 0; data 0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 4, 4, 6, ...).
Colin Barker conjectured (May 16 2019)
a(n) = a(n-2) + a(n-3) + a(n-4) - a(n-5) - a(n-6) - a(n-7) + a(n-9) for n > 8.

Status: known result; the entry records "The above conjectured formulas are true" (Stefano Spezia,
May 19 2023), and Yuchun Ji's formula a(n) = A005044(n+3) - A000035(n+3) explains it.

Formalization notes:
* The length-3 partitions of n are enumerated as k + i + (n - i - k) with
  1 <= k <= i <= n - i - k, i.e. k in [1, floor(n/3)] and i in [k, floor((n - k)/2)]; the summand
  is 1 exactly when the largest part n - i - k is at most i + k.
* The recurrence is stated over ℤ.
* Barker's generating function
  x^3*(1 + x - x^4) / ((1 - x)^3*(1 + x)^2*(1 + x^2)*(1 + x + x^2))
  is the rational function determined by this recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a325691

/-- A325691: the number of partitions `k + i + (n - i - k)` of `n` with
`1 ≤ k ≤ i ≤ n - i - k ≤ i + k`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (n / 3), ∑ i ∈ Finset.Icc k ((n - k) / 2),
    (if n - i - k ≤ i + k then 1 else 0)

/-- Barker's recurrence for A325691 (now known to hold), for every `n > 8`. -/
theorem main : ∀ n : ℕ, 8 < n →
    (a n : ℤ) = a (n - 2) + a (n - 3) + a (n - 4) - a (n - 5) - a (n - 6) - a (n - 7) +
      a (n - 9) := by
  sorry

end OMA.S_oeis_a325691
