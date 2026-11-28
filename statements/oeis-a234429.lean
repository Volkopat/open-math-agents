import Mathlib

/-!
# A234429: Numbers which are the digital sum of the square of some prime.

Source: https://oeis.org/A234429
Credit: @cblly (agent: Claude Code, model claude-opus-5-5)

The entry has offset 1 and data `4, 7, 9, 10, 13, 16, 19, 22, 25, 28, 31, 34, …`.
Its Formula section records:

  Conjectures from Chai Wah Wu, Apr 16 2025:
  a(n) = 2*a(n-1) - a(n-2) for n > 5.
  G.f.: x*(2*x^4 - x^3 - x^2 - x + 4)/(x - 1)^2.

Both conjectures are formalized, as a conjunction.

Conventions.
- The digital sum is the sum of the decimal digits.
- `a n` is the `n`-th such number in increasing order, counting from `1`:
  `Nat.nth IsTerm (n - 1)`. The first 20 terms agree with the entry (checked by computer).
- The recurrence is stated in `ℤ`, so the subtraction is not truncated.
- The generating function `∑_{n ≥ 1} a(n) x^n` is stated as a formal power series over `ℤ` whose
  coefficient of `x ^ 0` is `0`, multiplied out by the denominator `(x - 1) ^ 2`.
-/

namespace OMA.S_oeis_a234429

open PowerSeries

/-- The sum of the decimal digits of `m`. -/
def digitSum (m : ℕ) : ℕ :=
  (Nat.digits 10 m).sum

/-- `s` is the digital sum of the square of some prime. -/
def IsTerm (s : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ digitSum (p ^ 2) = s

/-- `a n`, the `n`-th term of A234429 (offset 1, so `a 1 = 4`). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth IsTerm (n - 1)

/-- Chai Wah Wu's conjectures: `a(n) = 2 a(n-1) - a(n-2)` for `n > 5`, and the generating function
`x (2x^4 - x^3 - x^2 - x + 4) / (x - 1)^2`. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 2 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ)) ∧
    ((X - 1) ^ 2 * PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) =
      X * (2 * X ^ 4 - X ^ 3 - X ^ 2 - X + 4)) := by
  sorry

end OMA.S_oeis_a234429
