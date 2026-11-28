import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# OEIS A218981: Four summands preserving the divisor sum

Source: https://oeis.org/A218981
Credit: @maaaakks

The listed integers are the sums of four positive integers for which the
sum of their divisor sums equals the divisor sum of the original integer.
The conjecture is that there are infinitely many such integers.
-/

namespace OMA.S_oeis_a218981

abbrev sigma (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

def IsTerm (n : ℕ) : Prop :=
  ∃ w x y z : ℕ, 0 < w ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
    n = w + x + y + z ∧ sigma n = sigma w + sigma x + sigma y + sigma z

theorem main : Set.Infinite {n : ℕ | IsTerm n} := by
  sorry

end OMA.S_oeis_a218981
