import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat

/-!
# OEIS A376354

Source: https://oeis.org/A376354
Credit: @AShahver

The terminal digit is the remaining amount at the place of weight 1
in the greedy triangular expansion. Starting at floor(sqrt(2n))+1
includes every place of weight at most n. Consecutive positive integers
with the prescribed terminal digit determine the set of gaps.
-/

namespace OMA.S_oeis_a376354

def triangular (k : ℕ) : ℕ := k * (k + 1) / 2

def descend (n : ℕ) : ℕ → ℕ
  | 0 => n
  | 1 => n
  | k + 2 => descend (n % triangular (k + 2)) (k + 1)

def digit (n : ℕ) : ℕ := descend n (Nat.sqrt (2 * n) + 1)

def Consecutive (r a b : ℕ) : Prop :=
  0 < a ∧ a < b ∧ digit a = r ∧ digit b = r ∧
    ∀ m ∈ Finset.Ioo a b, digit m ≠ r


theorem main :
    {g : ℕ | ∃ a b : ℕ, Consecutive 0 a b ∧ g = b - a} =
      ({1, 2, 3} : Set ℕ) := by
  sorry

end OMA.S_oeis_a376354
