import Mathlib

/-!
# A263613: Palindromic numbers in base 4 that are cubes.

Source: https://oeis.org/A263613
Credit: @cblly (agent: Claude Code, model claude-opus-5-5)

The entry has offset 1 and lists the terms written in base 4:
`0, 1, 1331, 1030301, 1003003001, 1000300030001, …` (for example `1331` is `125 = 5 ^ 3`).
Its Formula section records:

  Conjectures from Chai Wah Wu, Dec 25 2023:
  a(n) = 1111*a(n-1) - 112110*a(n-2) + 1111000*a(n-3) - 1000000*a(n-4) for n > 6.
  G.f.: x^2*(-7000000*x^4 + 6446000*x^3 - 336330*x^2 + 220*x + 1)/((x - 1)*(10*x - 1)*(100*x - 1)*(1000*x - 1)).

Both conjectures are formalized, as a conjunction.

Conventions.
- The listed terms are base-4 representations, so the recurrence and the generating function are
  about those digit strings read as decimal numbers. `term n` is the `n`-th cube (counting from
  `1`) whose base-4 digits form a palindrome, and `a n` is `term n` written in base 4 and read in
  base 10: `Nat.ofDigits 10 (Nat.digits 4 (term n))`.
- `0` (empty digit list) is a base-4 palindrome and a cube, so `a 1 = 0`, `a 2 = 1`,
  `a 3 = 1331`, matching the entry (checked by computer for the first eight terms).
- The recurrence is stated in `ℤ`, so the subtraction is not truncated.
- The generating function `∑_{n ≥ 1} a(n) x^n` is stated as a formal power series over `ℤ` whose
  coefficient of `x ^ 0` is `0`, multiplied out by its denominator.
-/

namespace OMA.S_oeis_a263613

open PowerSeries

/-- The base-4 digits of `m` read the same forwards and backwards. -/
def IsBase4Palindrome (m : ℕ) : Prop :=
  (Nat.digits 4 m).reverse = Nat.digits 4 m

/-- `m` is a cube whose base-4 representation is a palindrome. -/
def IsTerm (m : ℕ) : Prop :=
  (∃ r : ℕ, r ^ 3 = m) ∧ IsBase4Palindrome m

/-- The `n`-th such number (offset 1, so `term 1 = 0`). -/
noncomputable def term (n : ℕ) : ℕ :=
  Nat.nth IsTerm (n - 1)

/-- `a n` as listed in the entry: `term n` written in base 4, read as a decimal numeral. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 4 (term n))

/-- Chai Wah Wu's conjectures: the order-4 linear recurrence for `n > 6`, and the rational
generating function. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 1111 * (a (n - 1) : ℤ) - 112110 * (a (n - 2) : ℤ) +
        1111000 * (a (n - 3) : ℤ) - 1000000 * (a (n - 4) : ℤ)) ∧
    ((X - 1) * (10 * X - 1) * (100 * X - 1) * (1000 * X - 1) *
        PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) =
      X ^ 2 * (-7000000 * X ^ 4 + 6446000 * X ^ 3 - 336330 * X ^ 2 + 220 * X + 1)) := by
  sorry

end OMA.S_oeis_a263613
