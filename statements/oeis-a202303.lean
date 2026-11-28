import Mathlib

/-!
# A202303: a linear recurrence for the squares in A023110 with the last digit dropped

Source: https://oeis.org/A202303
Credit: @sntntHb

A023110 lists, in increasing order, the squares that remain squares when their last decimal digit
is removed (for a one-digit square the removal leaves `0`, which counts as a square):
`0, 1, 4, 9, 16, 49, 169, 256, 361, 1444, ...`. A202303 (offset 1) drops the last digit of
these: `a(n) = floor(A023110(n) / 10)`, giving `0, 0, 0, 0, 1, 4, 16, 25, 36, 144, ...`.
The entry records the conjecture (Colin Barker)
  `a(n) = 1443*a(n-7) - 1443*a(n-14) + a(n-21)`.

Removing the last digit of `s` gives `s / 10` (natural-number division), so A023110 is the
increasing enumeration of `{s | IsSquare s ∧ IsSquare (s / 10)}`, and `A023110(n)` is
`Nat.nth` of that predicate at `n - 1`. The set is infinite (e.g. `(10 m)^2`), so `Nat.nth`
enumerates it. The recurrence fails at `n = 22` and
holds numerically from `n = 23` on; it is stated for `n ≥ 23`, over the integers.
-/

namespace OMA.S_oeis_a202303

/-- `s` is a square that remains a square when its last decimal digit is removed. -/
def IsA023110 (s : ℕ) : Prop := IsSquare s ∧ IsSquare (s / 10)

/-- `a n = A023110(n) / 10` (offset 1; OEIS A202303). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsA023110 (n - 1) / 10

/-- Barker's conjecture in OEIS A202303, for `n ≥ 23`. -/
theorem main : ∀ n : ℕ, 23 ≤ n →
    (a n : ℤ) = 1443 * a (n - 7) - 1443 * a (n - 14) + a (n - 21) := by
  sorry

end OMA.S_oeis_a202303
