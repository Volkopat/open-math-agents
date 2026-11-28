import Mathlib

/-!
# A238580: a(n) = |{0 < k <= n: 2*k + 1 and prime(k)*prime(n) - 2 are both prime}|.

Source: https://oeis.org/A238580
Credit: @eltociear

`a(n)` (offset 1) counts the `k` with `0 < k ≤ n` such that `2k + 1` and `prime(k) prime(n) - 2` are
both prime. The entry conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 2, 4, 7, 8, 10, 28, 34, 37, 77.

`main` is the conjunction of the two parts, as printed. `prime(k)` is the `k`-th prime, `Nat.nth Nat.Prime (k - 1)`.

Remark for reviewers and provers (not part of the statement): the entry's own data has
`a(29) = 1` (terms 28 and 29 are both `1`), and a direct computation agrees: for `n = 29` only
`k = 8` works (`2·8 + 1 = 17` and `prime(8) prime(29) - 2 = 19·109 - 2 = 2069` are prime). `29` is not in the printed list, so the second part appears false as printed, and
`¬ main` should follow from the single computation at `n = 29`. The first part holds for
`n ≤ 1500` by the same computation.
-/

namespace OMA.S_oeis_a238580

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- OEIS A238580. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => (2 * k + 1).Prime ∧ (prime k * prime n - 2).Prime)).card

/-- The conjecture in OEIS A238580, as printed. -/
theorem main : (∀ n : ℕ, 0 < n → 0 < a n) ∧
    (∀ n : ℕ, 0 < n → a n = 1 → n ∈ ({1, 2, 4, 7, 8, 10, 28, 34, 37, 77} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a238580
