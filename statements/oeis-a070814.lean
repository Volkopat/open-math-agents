import Mathlib

/-!
# A070814: Solutions to phi(gpf(x)) - gpf(phi(x)) = 14

Source: https://oeis.org/A070814
Credit: @sobrien032

The entry (Labos Elemer, 2002) lists, in increasing order, the positive integers `x` with
`phi(gpf(x)) - gpf(phi(x)) = 14`, where `phi` is Euler's totient function (A000010) and `gpf n`
is the greatest prime factor of `n` (A006530), with the OEIS convention `gpf 1 = 1`. The
difference is taken in the integers. The offset is 1: `a(1) = 17`, `a(2) = 34`, ...,
`a(10) = 255`, `a(11) = 272`, `a(12) = 340`.

Conjecture (Ralf Stephan, May 09 2004, in the entry's formula section): for n > 10,
a(n) = 2 a(n-4).

Below, `a n` is the solution of index `n - 1` in increasing order (`Nat.nth` counts from 0),
so `a n` is the `n`-th term for every `n ≥ 1`; the statement only uses `n ≥ 7`.
-/

namespace OMA.S_oeis_a070814

/-- The greatest prime factor of `n` (OEIS A006530), with `gpf 1 = 1`. -/
def gpf (n : ℕ) : ℕ := if n = 1 then 1 else n.primeFactors.sup id

/-- `x` is a term: `x` is positive and `phi(gpf x) - gpf(phi x) = 14`, the difference taken in `ℤ`. -/
def IsTerm (x : ℕ) : Prop :=
  0 < x ∧ (Nat.totient (gpf x) : ℤ) - (gpf (Nat.totient x) : ℤ) = 14

/-- A070814(n) for `n ≥ 1`: the `n`-th term in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Stephan's conjecture: `a(n) = 2 a(n-4)` for every `n > 10`. -/
theorem main : ∀ n : ℕ, 10 < n → a n = 2 * a (n - 4) := by
  sorry

end OMA.S_oeis_a070814
