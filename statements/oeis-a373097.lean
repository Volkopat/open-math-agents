import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity

/-!
# Two conjectures about first differences of A373097

Source: https://oeis.org/A373097. Conjectures by Clark Kimberling, July 2024.
Credit: @jiyongparkphysics.

The source program uses exponents 1 through n, and takes exact floors of
natural numbers times the rational powers (2/3)^j. We use natural-number
division to take these floors. The equality and inequality involving
successive terms express the differences over the integers.
-/

namespace OMA.S_oeis_a373097

def a (n : ℕ) : ℕ :=
  if hn : n = 0 then 0 else if n = 1 then 1 else
    ∑ j ∈ Finset.range n, a (n * 2^(j+1) / 3^(j+1))
termination_by n
decreasing_by
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
  exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left (by decide) (Nat.succ_ne_zero _))
    (Nat.pos_of_ne_zero hn)

theorem main :
    (∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧ a (n+1) = a n + 1) ∧
    (∀ B : ℕ, ∃ n : ℕ, a n + B < a (n+1)) := by
  sorry

end OMA.S_oeis_a373097
