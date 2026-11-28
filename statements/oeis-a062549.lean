import Mathlib

/-!
# A062549: a(n) is the smallest number m such that m! is divisible by the left factorial !n (A003422).

Source: https://oeis.org/A062549
Credit: @divmxnd0x

Conjecture (Sean A. Irvine, Apr 01 2023, stated in A062549): `a(n)` is the largest prime factor of
`!n` for all `n > 2`.

Formalization notes:
* The data `a(0), a(1), ... = 1, 2, 4, 5, 17, 11, 23, ...` correspond to the sums
  `S(n) = 0! + 1! + ... + n!` (`1, 2, 4, 10, 34, 154, 874, ...`, the left factorial `!(n+1)` in the
  convention of A003422); this indexing is used here, so that `a n` is the least `m` with
  `S(n) ∣ m!`.
* The largest prime factor of `N ≥ 2` is the greatest prime dividing `N`.
-/

namespace OMA.S_oeis_a062549

/-- `S n = 0! + 1! + ... + n!`. -/
def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), k.factorial

/-- A062549(n): the least `m` such that `S n ∣ m!`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | S n ∣ m.factorial}

/-- The largest prime factor of `N`. -/
noncomputable def largestPrimeFactor (N : ℕ) : ℕ := sSup {p : ℕ | p.Prime ∧ p ∣ N}

/-- Irvine's conjecture: for `n > 2`, `a n` is the largest prime factor of `S n`. -/
theorem main : ∀ n : ℕ, 2 < n → a n = largestPrimeFactor (S n) := by
  sorry

end OMA.S_oeis_a062549
