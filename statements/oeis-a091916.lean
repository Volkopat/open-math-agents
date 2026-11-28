import Mathlib

/-!
# A091916: maximum of odd products of partitions of n

Source: https://oeis.org/A091916
Credit: @sntntHb

`a(n)` is the maximum, over all partitions of `n` whose product of parts is odd, of that product
(offset 0; the empty partition of `0` has product `1`, so `a(0) = 1`). The data begins
`1, 1, 1, 3, 3, 5, 9, 9, 15, 27, 27, 45, 81, ...`; e.g. the partitions of `5` have products
`5, 4, 6, 3, 4, 2, 1` and the maximal odd product is `5`.

The entry records the conjecture (Ralf Stephan, Dec 02 2004):
for `n > 5`, `a(n+3) = 3 * a(n)`.

Every `n` has the partition into `n` ones, of odd product `1`, so the set of odd products is
nonempty and `a(n)` is the supremum (a maximum) of a nonempty finite set of naturals.
`main` states the conjecture over the range `n > 5` given in the entry.
-/

namespace OMA.S_oeis_a091916

/-- `a n`: the maximal odd product of the parts of a partition of `n` (OEIS A091916). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => Odd p.parts.prod)).sup
    (fun p => p.parts.prod)

/-- Conjecture of OEIS A091916: `a(n+3) = 3 a(n)` for `n > 5`. -/
theorem main : ∀ n : ℕ, 5 < n → a (n + 3) = 3 * a n := by
  sorry

end OMA.S_oeis_a091916
