import Mathlib

/-!
# Numbers equal to the sum of the factorials of their decimal digits

Source: https://mathoverflow.net/questions/457007
Asked by MathOverflow user Jackson Walters.

Let `f` send a number `x = ∑_k x_k 10^k` (decimal digits `x_k`) to `∑_k x_k!`. The question
concerns the fixed points of `f`, i.e. the numbers that are the sum of the factorials of their
own digits, and states that the only nontrivial fixed points are `145` and `40585`. The asker
asks whether this can be shown by a general principle (a fixed point theorem) rather than by a
brute force search; that methodological request is not a formal statement, so this file
formalizes the claim about the fixed points itself.

Translation choices.
* Digits are taken from `Nat.digits 10`, and `f x` is the sum of the factorials of the
  decimal digits of `x`.
* Only positive integers are considered. (In Lean `Nat.digits 10 0` is the empty list, so `0`
  would be a spurious fixed point; with the usual convention that `0` has the digit `0`, it is
  not a fixed point since `0! = 1`.)
* The trivial fixed points are `1 = 1!` and `2 = 2!`, so the claim is that the positive fixed
  points of `f` are exactly `1`, `2`, `145` and `40585`.
-/

namespace OMA.S_mo_457007

/-- The sum of the factorials of the decimal digits of `x`. -/
def f (x : ℕ) : ℕ := ((Nat.digits 10 x).map Nat.factorial).sum

theorem main :
    ∀ x : ℕ, 0 < x → (f x = x ↔ x = 1 ∨ x = 2 ∨ x = 145 ∨ x = 40585) := by
  sorry

end OMA.S_mo_457007
