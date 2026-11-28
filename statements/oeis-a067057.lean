import Mathlib

/-!
# A067057: sums of products of the element sums of the two parts of {1,...,n}

Source: https://oeis.org/A067057
Credit: @jagong-cmu

Definition (OEIS): consider the set `N = {1,2,...,n}`; let `S` and `S'` be subsets of `N` such
that `S ∪ S' = N` (and `S`, `S'` disjoint); define `prod(S) = (sum of members of S) *
(sum of members of S')`; then `a(n)` is the sum of all possible `prod(S)`.

The entry gives the conjecture (Maksym Voznyy, Jul 26 2009)
Conjecture: G.f.: (-2*x^2*(x+1))/(2*x-1)^5.

Conventions:
* Offset 1, as in the entry (data: 0, 2, 22, 140, 680, ...).
* The worked example in the entry (n = 4, a(4) = 140) counts each split `{S, S'}` once, as an
  unordered pair: the split `S = {1}`, `S' = {2,3,4}` and the split `S = {2,3,4}`, `S' = {1}`
  are the same. A sum over all subsets `S` of `N` counts every unordered split exactly twice
  (`S` is never equal to its complement when `n ≥ 1`), so `a n` is that sum divided by `2`.
  This sum is even, so the floor division `/ 2` on `ℕ` is exact. The empty split
  (`S = ∅`) gives the product `0`, so it does not change the sum.
* The generating function of a sequence with offset 1 is `Sum_{n>=1} a(n) x^n`. The series `A`
  below has coefficient `0` at `x^0` and `a(n)` at `x^n` for `n ≥ 1`.
* The identity is stated in `ℤ[[x]]` with the denominator cleared:
  `A * (2x - 1)^5 = -2x^2(x + 1)`. The series `(2x - 1)^5` has constant coefficient `-1`,
  a unit of `ℤ`, so this form is equivalent to the quotient form.
-/

namespace OMA.S_oeis_a067057

open PowerSeries

/-- `a(n)`: half the sum, over all subsets `S` of `{1,...,n}`, of
`(sum of S) * (sum of the complement of S)`. -/
def a (n : ℕ) : ℕ :=
  (∑ S ∈ (Finset.Icc 1 n).powerset, (∑ i ∈ S, i) * (∑ i ∈ Finset.Icc 1 n \ S, i)) / 2

/-- The generating function `Sum_{n>=1} a(n) x^n`, with offset 1. -/
noncomputable def A : PowerSeries ℤ := mk fun n => if n = 0 then 0 else (a n : ℤ)

/-- The generating function of A067057 is `-2*x^2*(x+1)/(2*x-1)^5`. -/
theorem main : A * (2 * X - 1) ^ 5 = -2 * X ^ 2 * (X + 1) := by
  sorry

end OMA.S_oeis_a067057
