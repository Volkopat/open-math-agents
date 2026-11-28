import Mathlib

/-!
# A117547: Numbers k such that 2*k^2+1 is a perfect power.

Source: https://oeis.org/A117547
Credit: @cblly (agent: Claude Code, model claude-opus-5-5)

The entry has offset 1 and data `0, 2, 11, 12, 70, 408, 2378, 13860, 80782, …`, so `a 1 = 0`,
`a 2 = 2`, `a 3 = 11`, `a 4 = 12`, `a 5 = 70`. Its Formula section records:

  Conjectures from Colin Barker, Apr 28 2012:
  a(n) = 6*a(n-1) - a(n-2) for n > 5.
  G.f.: x^2*(2-x-52*x^2+9*x^3)/ (1-6*x+x^2).

Both conjectures are formalized, as a conjunction.

Conventions.
- A perfect power is `m ^ e` with `e ≥ 2` and any base, as in OEIS A001597, which counts
  `1 = 1 ^ 2`. This is why `k = 0` (with `2 * 0 ^ 2 + 1 = 1`) is the first term. With this
  definition the terms below `10 ^ 5` are exactly `0, 2, 11, 12, 70, 408, 2378, 13860, 80782`,
  matching the entry.
- `a n` is the `n`-th term counting from `1`, i.e. `Nat.nth isTerm (n - 1)`.
- The recurrence is stated in `ℤ`, so the subtraction is not truncated.
- The generating function `∑_{n ≥ 1} a(n) x^n` is stated as a formal power series over `ℤ` whose
  coefficient of `x ^ 0` is `0` (the sequence starts at `n = 1`), multiplied out by the
  denominator `1 - 6x + x^2`.
-/

namespace OMA.S_oeis_a117547

open PowerSeries

/-- `n` is a perfect power: `n = m ^ e` for some `m` and some `e ≥ 2` (so `0` and `1` count). -/
def IsPerfectPower (n : ℕ) : Prop :=
  ∃ m e : ℕ, 2 ≤ e ∧ m ^ e = n

/-- `k` is a term of A117547: `2 * k ^ 2 + 1` is a perfect power. -/
def isTerm (k : ℕ) : Prop :=
  IsPerfectPower (2 * k ^ 2 + 1)

/-- `a n`, the `n`-th term of A117547 (offset 1, so `a 1 = 0`). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth isTerm (n - 1)

/-- Colin Barker's conjectures: the recurrence `a(n) = 6 a(n-1) - a(n-2)` for `n > 5`, and the
generating function `x^2 (2 - x - 52 x^2 + 9 x^3) / (1 - 6x + x^2)`. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ)) ∧
    ((1 - 6 * X + X ^ 2) * PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) =
      X ^ 2 * (2 - X - 52 * X ^ 2 + 9 * X ^ 3)) := by
  sorry

end OMA.S_oeis_a117547
