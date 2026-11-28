import Mathlib

/-!
# A204519: Square root of floor(A055851(n)/6).

Source: https://oeis.org/A204519
Credit: @SPatel2133

Conjecture (Vaclav Kotesovec, Nov 26 2012): for n >= 8, a(n) = 10*a(n-3) - a(n-6).
Empirical g.f. (Colin Barker, Sep 15 2014): x^4*(x^3+4*x^2+2*x+1) / (x^6-10*x^3+1).

A055851 lists, in increasing order and with offset one, the numbers m such that m and
floor(m/6) are both squares: 0, 1, 4, 9, 25, 100, 729, ... Here it is `Nat.nth` of that
predicate, shifted to offset one. Then a(n) = sqrt(floor(A055851(n)/6)), with offset one:
0, 0, 0, 1, 2, 4, 11, 20, 40, ... `Nat.sqrt` is exact here because the argument is a square.
The sequence is padded with `a 0 = 0`, the constant coefficient of the generating function.
The values are cast to `ℤ` so that the subtraction is exact. The generating function is stated
with its denominator cleared.
-/

namespace OMA.S_oeis_a204519

open PowerSeries

/-- A055851 with offset one: the `n`-th number `m` such that `m` and `m / 6` are squares. -/
noncomputable def A055851 (n : ℕ) : ℕ :=
  Nat.nth (fun m => IsSquare m ∧ IsSquare (m / 6)) (n - 1)

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.sqrt (A055851 n / 6)

theorem main :
    (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 10 * a (n - 3) - a (n - 6)) ∧
    ((X ^ 6 - 10 * X ^ 3 + 1) * PowerSeries.mk (fun n => (a n : ℤ)) =
      (X ^ 4 * (X ^ 3 + 4 * X ^ 2 + 2 * X + 1) : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a204519
