import Mathlib

/-!
# A301877: sums of the groups of natural numbers with Narayana-cows sizes

Source: https://oeis.org/A301877 (conjectures by Colin Barker, Mar 28 2018)

Entry (offset 1): Group the natural numbers into groups (1),(2),(3),(4),(5,6),(7,8,9),... so
that the n-th group contains N(n) terms, where N(n) is the Narayana's cows sequence (A000930).
Sequence contains the sum of the terms in the n-th group.
Formula section, Conjectures from Colin Barker, Mar 28 2018:
G.f.: x*(1 - x)*(1 + x - 5*x^3 - 5*x^4 - 3*x^5 + x^6 + 2*x^7 + x^8) / ((1 + x^2 - x^3)*(1 - x - x^3)*(1 - x - 2*x^2 - x^3)).
a(n) = 7*a(n-1) - 18*a(n-2) + 20*a(n-3) - 6*a(n-4) - 6*a(n-5) + 5*a(n-6) - a(n-7) for n>10.

Formalization notes:
* A000930 (offset 0) is `N(0) = N(1) = N(2) = 1`, `N(k) = N(k-1) + N(k-3)`, i.e. 1, 1, 1, 2, 3, 4, 6, ...
* The groups are consecutive blocks of the positive integers. As the listed groups
  (1),(2),(3),(4),(5,6),(7,8,9) show, their sizes are 1, 1, 1, 1, 2, 3, 4, 6, ..., that is,
  group 1 has 1 term and group n has N(n-2) terms for n >= 2 (this matches the entry formula
  a(n) = (2N(n)+N(n-2)+1)*N(n-2)/2 for n > 1 and the data). Group n starts at
  `1 + (sizes of groups 1..n-1)`, and a(n) is the sum of its terms.
* With offset 1 the generating function is `A(x) = Sum_(n >= 1) a(n) x^n`, the power series with
  coefficient 0 at `x^0`; since the denominator has constant term 1, `A = N/D` is stated as
  `A * D = N` in the formal power series ring over the integers.
* The recurrence is stated with the range n > 10 given in the entry, in the integers.
* Controls from the entry: a(1..11) = 1, 2, 3, 4, 11, 24, 46, 99, 216, 455, 969.
-/

namespace OMA.S_oeis_a301877

open PowerSeries

/-- Narayana's cows sequence A000930. -/
def N : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | k + 3 => N (k + 2) + N k

/-- The number of terms of group `n` (groups are numbered from 1). -/
def size (n : ℕ) : ℕ := if n ≤ 1 then 1 else N (n - 2)

/-- The first term of group `n`. -/
def first (n : ℕ) : ℕ := 1 + ∑ k ∈ Finset.Ico 1 n, size k

/-- A301877(n): the sum of the terms of group `n`. -/
def a (n : ℕ) : ℕ := ∑ j ∈ Finset.range (size n), (first n + j)

/-- Barker's generating function and recurrence. -/
theorem main :
    mk (fun n => if n = 0 then 0 else (a n : ℤ)) *
        ((1 + X ^ 2 - X ^ 3) * (1 - X - X ^ 3) * (1 - X - 2 * X ^ 2 - X ^ 3)) =
      (X * (1 - X) * (1 + X - 5 * X ^ 3 - 5 * X ^ 4 - 3 * X ^ 5 + X ^ 6 + 2 * X ^ 7 + X ^ 8) :
        PowerSeries ℤ) ∧
    ∀ n : ℕ, 10 < n →
      (a n : ℤ) = 7 * a (n - 1) - 18 * a (n - 2) + 20 * a (n - 3) - 6 * a (n - 4) -
        6 * a (n - 5) + 5 * a (n - 6) - a (n - 7) := by
  sorry

end OMA.S_oeis_a301877
