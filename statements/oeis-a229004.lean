import Mathlib

/-!
# A229004: indices of Bell numbers divisible by 3

Source: https://oeis.org/A229004 (conjectures by Colin Barker, Jul 16 2014)

`a(n)` (offset 1, so `a(1) = 4`) is the n-th nonnegative integer `m`, in increasing order,
with `3 ∣ Bell(m)`; Bell numbers are Mathlib's `Nat.bell` (`Bell(0) = 1`). Since `Nat.nth`
is 0-indexed, `a n = Nat.nth (fun m => 3 ∣ Nat.bell m) (n - 1)`.

The conjectures:
* the recurrence `a(n) = a(n-1) + a(n-4) - a(n-5)`, stated for `n >= 6` (the first index for
  which every term is defined with offset 1);
* the g.f. `Sum_{n>=1} a(n) x^n = x*(2x^4+2x^3+x^2+4x+4) / ((x-1)^2 (x+1) (x^2+1))`, written
  without division as an identity of integer power series (the coefficient of `x^0` on the
  left is `0`, as the sequence starts at `n = 1`).
-/

namespace OMA.S_oeis_a229004

open PowerSeries

/-- A229004 (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m => 3 ∣ Nat.bell m) (n - 1)

theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
        ((X - 1) ^ 2 * (X + 1) * (X ^ 2 + 1)) =
      X * (2 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + 4 * X + 4) := by
  sorry

end OMA.S_oeis_a229004
