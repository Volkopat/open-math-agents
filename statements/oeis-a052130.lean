import Mathlib

/-!
# OEIS A052130: when is `m` 'sufficiently large'?

Source: https://oeis.org/A052130
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `N(m, n)` be the number of integers in `[1, 2^m]` with exactly `m - n` prime factors (with
multiplicity); for fixed `n` it is constant for `m` sufficiently large, and A052130 lists the
limits. The entry states (a conjecture asked about by R. G. Wilson v, see A126281) that `m` is
sufficiently large precisely when `2^m > 3^(m-n)`, for `n > 1`.

Conventions:
* '`m` is sufficiently large' means `N(m', n) = N(m, n)` for every `m' ≥ m`. `m ≥ n` (so that
  `m - n` is a genuine count), `n ≥ 2`.
-/

namespace OMA.S_oeis_a052130

/-- `N(m, n) = #{k ∈ [1, 2^m] | Ω(k) = m - n}`. -/
def N (m n : ℕ) : ℕ :=
  ((Finset.Icc 1 (2 ^ m)).filter fun k => ArithmeticFunction.cardFactors k = m - n).card

/-- For `n ≥ 2` and `m ≥ n`: `N(·, n)` is constant from `m` on iff `2^m > 3^(m-n)`. -/
theorem main : ∀ n m : ℕ, 2 ≤ n → n ≤ m →
    ((∀ m' : ℕ, m ≤ m' → N m' n = N m n) ↔ 3 ^ (m - n) < 2 ^ m) := by
  sorry

end OMA.S_oeis_a052130
