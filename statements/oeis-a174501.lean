import Mathlib

/-!
# A174501: Continued fraction expansion for exp( Sum_{n>=1} 1/(n*A003499(n)) ), where A003499(n) = (3+sqrt(8))^n + (3-sqrt(8))^n.

Source: https://oeis.org/A174501
Credit: @maaaakks

## The conjecture

OEIS A174501 (offset 1) lists the simple continued fraction
`exp(L) = [1; 4, 1, 32, 1, 196, 1, 1152, ...]` of the constant
`exp(L)`, `L = Sum_{n>=1} 1/(n*A003499(n)) = 0.18330741135634946...`.
Its FORMULA section says:

> a(2n-1) = 1, a(2n) = A003499(n) - 2, for n>=1 [conjecture].
>
> The above conjectures are correct. See the Bala link for details.
> - _Peter Bala_, Jan 08 2013

## Definitions

* `A003499 n` is OEIS A003499, `a(n) = (3+sqrt 8)^n + (3-sqrt 8)^n`, defined here as an
  integer sequence by its recurrence `a(0) = 2`, `a(1) = 6`, `a(n+2) = 6 a(n+1) - a(n)`.
  Since `3 ± sqrt 8` are the roots of `t^2 - 6t + 1`, this recurrence gives exactly
  the closed form `(3+sqrt 8)^n + (3-sqrt 8)^n` (values 2, 6, 34, 198, 1154, ...).
* `x = exp (∑' n : ℕ, 1 / ((n+1) * A003499 (n+1)))` is the constant; the shift
  `n ↦ n+1` makes the summation range `n >= 1` as in OEIS. The series has positive terms
  bounded by `(3+sqrt 8)^(-n)`, so it is summable and `tsum` is its genuine value.

## Continued fraction API and indexing

Mathlib's `GenContFract.of v` is the (regular) continued fraction of a real `v`:
`(GenContFract.of v).h = ⌊v⌋` is the integer part, and `(GenContFract.of v).s` is the
sequence of pairs `⟨1, b_i⟩` (partial numerators are always `1`), so
`(GenContFract.of v).partDens.get? i` is the `i`-th partial denominator `b_i`
(0-indexed), and is `none` once the expansion has terminated.
Thus `v = h + 1/(b_0 + 1/(b_1 + ...))`.

OEIS uses offset 1 and includes the integer part as its first term:
`a(1) = 1 = ⌊exp L⌋`, `a(2) = 4 = b_0`, `a(3) = 1 = b_1`, ..., i.e.
`a(1) = h` and `a(k) = b_(k-2)` for `k >= 2`. The helper `oeisTerm v k` encodes exactly this
dictionary (returning `none` for the nonexistent index `0`). The theorem states that for
every `n >= 1` the terms `a(2n-1)` and `a(2n)` exist and equal `1` and `A003499(n) - 2`,
respectively; in particular the expansion is infinite.
-/

namespace OMA.S_oeis_a174501

/-- OEIS A003499: `a(n) = (3+sqrt 8)^n + (3-sqrt 8)^n`, via `a(n+2) = 6 a(n+1) - a(n)`. -/
def A003499 : ℕ → ℤ
  | 0 => 2
  | 1 => 6
  | n + 2 => 6 * A003499 (n + 1) - A003499 n

/-- The constant `exp (Sum_{n>=1} 1/(n * A003499 n))`. -/
noncomputable def x : ℝ :=
  Real.exp (∑' n : ℕ, 1 / (((n : ℝ) + 1) * (A003499 (n + 1) : ℝ)))

/-- The `k`-th term (OEIS offset 1) of the simple continued fraction of `v`:
`a(1)` is the integer part, `a(k)` for `k >= 2` is the `(k-2)`-th partial denominator
of Mathlib's `GenContFract.of v`. -/
noncomputable def oeisTerm (v : ℝ) (k : ℕ) : Option ℝ :=
  if k = 0 then none
  else if k = 1 then some ((GenContFract.of v).h)
  else (GenContFract.of v).partDens.get? (k - 2)

theorem main : ∀ n : ℕ, 1 ≤ n →
    oeisTerm x (2 * n - 1) = some 1 ∧
    oeisTerm x (2 * n) = some ((A003499 n : ℝ) - 2) := by
  sorry

end OMA.S_oeis_a174501
