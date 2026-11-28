import Mathlib

/-!
# A048610: Smallest number that is the sum of two positive squares in >= n ways.

Source: https://oeis.org/A048610
Credit: @Nir135

The conjecture listed in the entry (Bill McEachen, Nov 08 2026):
* a(n) ends in 5 for n > 2 (verified for n <= 10^9).

Conventions of this translation.
* A way to write `m` as a sum of two positive squares is an unordered pair: `m = x^2 + y^2`
  with `0 < x ≤ y`. This is the convention of the OEIS data: for example a(2) = 50, since
  `50 = 1^2 + 7^2 = 5^2 + 5^2`, while `25 = 3^2 + 4^2` has only one such way (`0^2 + 5^2` is
  excluded). With it, the definition below reproduces all 29 listed terms (checked by computer).
* Offset 1, as in the entry: `a n` is the least positive integer with at least `n` ways.
  The set is nonempty for every `n` (the number of ways of `5^k` grows with `k`), so `sInf`
  is the minimum and never the default value `0`.
* Ends in 5 means that the last decimal digit is 5, that is `a n % 10 = 5`.
-/

namespace OMA.S_oeis_a048610

/-- The number of ways to write `m` as `x^2 + y^2` with `0 < x ≤ y`. -/
def ways (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter
    (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 = m)).card

/-- A048610: the smallest number that is the sum of two positive squares in at least `n` ways. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ≤ ways m}

/-- McEachen's conjecture for OEIS A048610: for `n > 2`, the last decimal digit of `a n` is 5. -/
theorem main : ∀ n : ℕ, 2 < n → a n % 10 = 5 := by
  sorry

end OMA.S_oeis_a048610
