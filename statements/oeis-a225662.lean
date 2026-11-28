import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Group.Nat.Even

/-!
# OEIS A225662

Source: https://oeis.org/A225662 and https://oeis.org/A225660
Credit: @jiyongparkphysics

The source proves that every orbit is eventually periodic with period dividing
six. Membership in the eventual cycle is therefore equivalent to returning to
the same vector after six updates, and is preserved by every subsequent update.
-/
namespace OMA.S_oeis_a225662

/-- Increment bucket i, extending the vector by zeros as needed. -/
def bump : ℕ → List ℕ → List ℕ
  | 0, [] => [1]
  | 0, x :: xs => (x+1) :: xs
  | i+1, [] => 0 :: bump i []
  | i+1, x :: xs => x :: bump i xs

def histogram (v : List ℕ) := v.foldr bump []

def digits (n : ℕ) := if n = 0 then [0] else (Nat.digits 4 n).reverse

/-- The first time the orbit enters its eventual cycle. -/
def hasPreperiod (v : List ℕ) (t : ℕ) : Prop :=
  let u := histogram^[t] v
  let previous := histogram^[t-1] v
  histogram^[6] u = u ∧ (t = 0 ∨ histogram^[6] previous ≠ previous)

theorem main : ∀ n t : ℕ, hasPreperiod (digits n) t → 6 < t → Odd t := by
  sorry

end OMA.S_oeis_a225662
