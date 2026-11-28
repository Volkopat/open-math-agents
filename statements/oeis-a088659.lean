import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Bounds.Defs

/-!
# The period proposed in OEIS A088659

Source: https://oeis.org/A088659 (Benoit Cloitre, OEIS Foundation, CC BY-SA 4.0).
The sequence starts at n = 2. The linked sequence A088957 is evaluated by the
finite sum on its OEIS page, with the substitution j = k - i. Its j = 0
summand is 1, also obtained by natural-number subtraction in the exponent.
A period of the tail means a positive shift that works for every k > n.
-/

namespace OMA.S_oeis_a088659

def b (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), k.choose j * (j + 1) ^ (j - 1)

def proposedPeriod (n : ℕ) : ℕ :=
  n * (n.primeFactorsList.foldl max 0 - 1)

def tailPeriods (n : ℕ) : Set ℕ :=
  {t | 0 < t ∧ ∀ k : ℕ, n < k → b (k + t) % n = b k % n}

theorem main : ∀ n : ℕ, 2 ≤ n → IsLeast (tailPeriods n) (proposedPeriod n) := by
  sorry

end OMA.S_oeis_a088659
