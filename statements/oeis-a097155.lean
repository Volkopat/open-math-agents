import Mathlib

/-!
# A097155: Numbers that reach the fixed point 89 under iteration of f(x) = reverse(x) - maxdigit(x)

Source: https://oeis.org/A097155
Credit: @xor2k

Formalizes the OEIS A097155 conjecture: It is conjectured that 0 and 89 are the only fixed points
of f, where f(x) = reverse(x) - maxdigit(x).

Conventions:
* `f` acts on nonnegative integers `x : ℕ`; `reverse(x)` reads the decimal digits of `x` backwards
  (leading zeros of the result drop out, so `reverse(120) = 21`), as in the Mathematica program
  `FromDigits[Reverse[IntegerDigits[n]]]`. Digits come from `Nat.digits 10`.
* `maxdigit(x)` is the largest decimal digit (`0` for `x = 0`).
* `reverse(x) ≥ maxdigit(x)` always holds, so the natural subtraction in `f` is the true value.
* The remark in the same comment that 89 is the first number that does not reach zero is a
  stated fact, not a conjecture, and is not formalized here.
-/

namespace OMA.S_oeis_a097155

/-- Decimal reversal: the number whose decimal digits are those of `x` in reverse order. -/
def rev (x : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 x).reverse

/-- Largest decimal digit of `x` (`0` for `x = 0`). -/
def maxDigit (x : ℕ) : ℕ :=
  (Nat.digits 10 x).foldr max 0

/-- The map `f(x) = reverse(x) - maxdigit(x)`. -/
def f (x : ℕ) : ℕ :=
  rev x - maxDigit x

/-- The only fixed points of `f` are `0` and `89`. -/
theorem main :
    ∀ x : ℕ, f x = x ↔ x = 0 ∨ x = 89 := by
  sorry

end OMA.S_oeis_a097155
