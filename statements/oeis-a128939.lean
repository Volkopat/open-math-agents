import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Order.Bounds.Defs

/-!
# Largest product of partition parts congruent to one modulo three

The set includes the product of every partition of n into positive
parts of the form 3k+1. Ordering the parts does not change this set.
The greatest-element formulation asserts both attainment and optimality.

Source: https://oeis.org/A128939
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a128939

def prediction (n : ℕ) : ℕ :=
  if n < 4 then 1
  else if n % 4 = 3 then 7 * 4 ^ (n / 4 - 1) else 4 ^ (n / 4)

def products (n : ℕ) : Set ℕ := {v | ∃ parts : List ℕ,
  (∀ p ∈ parts, p % 3 = 1) ∧ parts.sum = n ∧ parts.prod = v}

theorem main : ∀ n : ℕ, 1 ≤ n → IsGreatest (products n) (prediction n) := by
  sorry

end OMA.S_oeis_a128939
