import Mathlib

/-!
# A081237: Numbers n with no k, 0<k<n, such that mu(n-k)=mu(n)=mu(n+k), where mu=A008683 (Moebius function).

Source: https://oeis.org/A081237
Credit: @gblacher2

Conjecture (comment in A081237): "there are no more terms", that is, the terms
`1, 2, 3, 4, 6, 9, 15, 21` listed in the OEIS data are all the terms of the sequence.

Conventions:
* the offset of A081237 is 1, so the terms are positive integers `n ≥ 1`;
* `mu` is Mathlib's Möbius function `ArithmeticFunction.moebius` (A008683), with values in `ℤ`;
* for `0 < k < n` both `n - k` and `n + k` are positive, so the subtraction in `ℕ` is exact and
  `mu` is only evaluated at positive integers;
* `n = 1` is a term vacuously, since there is no `k` with `0 < k < 1`.

The OEIS also notes that a next term, if it exists, exceeds `10^10` (Sean A. Irvine, Sep 08 2009).
-/

namespace OMA.S_oeis_a081237

open ArithmeticFunction

/-- The defining property of A081237: no `k` with `0 < k < n` has
`mu(n - k) = mu(n) = mu(n + k)`. -/
def IsTerm (n : ℕ) : Prop :=
  ¬ ∃ k : ℕ, 0 < k ∧ k < n ∧ moebius (n - k) = moebius n ∧ moebius n = moebius (n + k)

/-- The conjecture: the only terms of A081237 are `1, 2, 3, 4, 6, 9, 15, 21`. -/
theorem main : {n : ℕ | 1 ≤ n ∧ IsTerm n} = {1, 2, 3, 4, 6, 9, 15, 21} := by
  sorry

end OMA.S_oeis_a081237
