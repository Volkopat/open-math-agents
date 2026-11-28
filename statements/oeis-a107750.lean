import Mathlib

/-!
# A107750: smallest number greater than its predecessor with a different number of binary zeros

Source: https://oeis.org/A107750
Credit: @jagong-cmu

THE CONJECTURE AS STATED IS FALSE. The recurrence part fails at n = 6:
a(6) = 7, but a(5) + a(3) - a(2) = 5 + 3 - 2 = 6.

The entry has the formula lines
Conjectures from Colin Barker, Jul 24 2017: (Start)
G.f.: x*(1+x)*(1+x^2-x^3+x^4) / ((1-x)^2*(1+x+x^2)).
a(n) = a(n-1) + a(n-3) - a(n-4) for n>3. (End)
This file states both conjectures exactly as written, as a conjunction, so that it can be
refuted. Data (offset 0): 0, 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 15, .... The recurrence holds
for all n > 6 but not for n = 6 (the numerator of the g.f. has degree 6, so the recurrence
follows from the g.f. only for n > 6).

Definition: a(0) = 0, and for n >= 1, a(n) is the smallest number greater than a(n-1) whose
binary representation has either more or fewer zeros than that of a(n-1).

Conventions:
* `zeros m` is the number of zeros in the binary representation of `m` (A023416), with the
  usual convention that `0` is written `0`, so `zeros 0 = 1`. For `m > 0` it is the number of
  `0` digits in `Nat.digits 2 m`.
* `a (n + 1) = sInf {m | a n < m ∧ zeros m ≠ zeros (a n)}`. The set is never empty
  (one of `a n + 1` and `2 * (a n + 1)` has a different number of zeros), so `sInf` is its least
  element.
* The recurrence is stated in `ℤ`, to avoid truncated subtraction. For `n > 3` the indices
  `n - 1`, `n - 3`, `n - 4` on `ℕ` are exact.
* The g.f. is `A = Sum_{n ≥ 0} a(n) x^n` in `PowerSeries ℤ`, with the denominator cleared:
  `A * ((1 - x)^2 * (1 + x + x^2)) = x * (1 + x) * (1 + x^2 - x^3 + x^4)`.
-/

namespace OMA.S_oeis_a107750

/-- The number of zeros in the binary representation of `m` (`0` is written `0`). -/
def zeros (m : ℕ) : ℕ := if m = 0 then 1 else (Nat.digits 2 m).count 0

/-- `a(0) = 0`; `a(n)` is the smallest number greater than `a(n-1)` with more or fewer
binary zeros than `a(n-1)`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => sInf {m | a n < m ∧ zeros m ≠ zeros (a n)}

/-- Barker's conjectures, as written: the g.f. `x(1+x)(1+x^2-x^3+x^4)/((1-x)^2(1+x+x^2))`
and `a(n) = a(n-1) + a(n-3) - a(n-4)` for `n > 3`. It is false (the recurrence fails at
`n = 6`). -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℤ)) *
        ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X + PowerSeries.X ^ 2)) =
      PowerSeries.X * (1 + PowerSeries.X) *
        (1 + PowerSeries.X ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 4)) ∧
    ∀ n : ℕ, 3 < n → (a n : ℤ) = a (n - 1) + a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a107750
