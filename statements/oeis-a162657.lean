import Mathlib

/-!
# A162657: every positive integer is the denominator of sigma(m)/m for some m

Source: https://oeis.org/A162657

A162657 (offset 1): `a(n)` is the least number `m` such that `n` is the denominator of
`sigma_{-1}(m) = sigma(m)/m` (in lowest terms), or zero if no such `m` exists:
1, 2, 3, 4, 5, 18, 7, 8, 9, 20, 11, 48, 13, 112, 45, …

Conjecture (Franklin T. Adams-Watters, Jul 08 2009): `a(n)` is never zero. That is, for every
positive integer `n` there is a positive integer `m` such that the denominator of `sigma(m)/m`
is `n`.

Conventions:
- `sigma(m)` is the sum of the divisors of `m`, written as `∑ d ∈ m.divisors, d`, and
  `sigma_{-1}(m) = sigma(m)/m` is formed in `ℚ`; `Rat.den` is the denominator in lowest terms.
- `n` and `m` are positive, as in the entry (offset 1, and `m` a positive integer).
-/

namespace OMA.S_oeis_a162657

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ m : ℕ, 0 < m ∧ (((∑ d ∈ m.divisors, d : ℕ) : ℚ) / (m : ℚ)).den = n := by
  sorry

end OMA.S_oeis_a162657
