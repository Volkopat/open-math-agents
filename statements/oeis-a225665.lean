import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Function.Iterate

/-!
# OEIS A225665

Source: https://oeis.org/A225665 and https://oeis.org/A225660
Credit: @jiyongparkphysics

The hexadecimal entry asks whether its preperiod is odd for only finitely many
inputs. The source's eventually-period-six theorem applies to every starting
vector, so a vector belongs to the periodic part exactly when six updates
return it to itself. This property persists under each further update.
-/
namespace OMA.S_oeis_a225665

/-- Increment bucket i, extending the vector with zeros as needed. -/
def bump : ℕ → List ℕ → List ℕ
  | 0, [] => [1]
  | 0, x :: xs => (x+1) :: xs
  | i+1, [] => 0 :: bump i []
  | i+1, x :: xs => x :: bump i xs

/-- Bucket i counts occurrences of i, up to and including the largest entry. -/
def histogram (v : List ℕ) := v.foldr bump []

/-- An even-numbered iterate lies outside the cycle and its successor lies inside. -/
def oddPreperiod (v : List ℕ) : Prop :=
  ∃ j : ℕ, let u := histogram^[2*j] v
           histogram^[6] u ≠ u ∧ histogram^[6] (histogram u) = histogram u

/-- Conventional most-significant-first digits, including the digit 0 for zero. -/
def hexadecimal (n : ℕ) := if n = 0 then [0] else (Nat.digits 16 n).reverse

theorem main : {n : ℕ | oddPreperiod (hexadecimal n)}.Finite := by
  sorry

end OMA.S_oeis_a225665
