import Mathlib

/-!
# A393168: Integers k which can be written in the form x^2 + y^2 - z^2, where x, y, z are integers and x^2, y^2, z^2 <= k.

Source: https://oeis.org/A393168
Credit: @luciusacarr

Data: 0, 1, 2, 4, 5, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, ...

The entry says: it is conjectured that every number greater than 6563 can be written in this
form. `main` states that conjecture.

Reading of the source:
* `k` is a natural number and `x, y, z` are integers with `x^2, y^2, z^2 ≤ k` and
  `k = x^2 + y^2 - z^2`.
* With this reading the terms below 90 match the data, and the numbers up to 30000 that are not
  of this form end with 3495, 4686, 5447, 5727, 6563 (checked numerically).
-/

namespace OMA.S_oeis_a393168

/-- `k` is of the form `x^2 + y^2 - z^2` with `x^2, y^2, z^2 ≤ k`. -/
def IsRepresentable (k : ℕ) : Prop :=
  ∃ x y z : ℤ, x ^ 2 ≤ k ∧ y ^ 2 ≤ k ∧ z ^ 2 ≤ k ∧ (k : ℤ) = x ^ 2 + y ^ 2 - z ^ 2

theorem main :
    -- Every number greater than 6563 can be written in this form.
    ∀ k : ℕ, 6563 < k → IsRepresentable k := by
  sorry

end OMA.S_oeis_a393168
