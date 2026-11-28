import Mathlib

/-!
# A091915: maximum of even products of partitions of n

Source: https://oeis.org/A091915
Credit: @sntntHb

`a(n)` is the maximum, over all partitions of `n` whose product of parts is even, of that product
(offset 1; `a(1) = 0` since the only partition of `1` has product `1`, so there is no even
product). The data begins `0, 2, 2, 4, 6, 8, 12, 18, 24, 36, 54, 72, ...`; e.g. the partitions
of `5` have products `5, 4, 6, 3, 4, 2, 1` and the maximal even product is `6`.

The entry records the conjecture (Ralf Stephan, Dec 02 2004):
for `n > 6`, `a(n+3) = 3 * a(n)`.

Here `a n` is the supremum of the even products of the partitions of `n` (a finite set of
naturals), which is `0` when there is none, matching `a(1) = 0`. `main` states the conjecture over
the range `n > 6` given in the entry.
-/

namespace OMA.S_oeis_a091915

/-- `a n`: the maximal even product of the parts of a partition of `n` (OEIS A091915). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => Even p.parts.prod)).sup
    (fun p => p.parts.prod)

/-- Conjecture of OEIS A091915: `a(n+3) = 3 a(n)` for `n > 6`. -/
theorem main : ∀ n : ℕ, 6 < n → a (n + 3) = 3 * a n := by
  sorry

end OMA.S_oeis_a091915
