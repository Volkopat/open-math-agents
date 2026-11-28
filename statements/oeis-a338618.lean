import Mathlib

/-!
# OEIS A338618

Source: https://oeis.org/A338618
Credit: @yuka30240

The OEIS sequence starts at index 1 and takes positive integer values.
-/

namespace OMA.S_oeis_a338618

/-- The terms are distinct, and every three consecutive terms contain a pair
with a common factor greater than one. -/
def Admissible (a : ℕ+ → ℕ+) : Prop :=
  Function.Injective a ∧ ∀ n : ℕ+,
    let x : ℕ := a n
    let y : ℕ := a (n + 1)
    let z : ℕ := a (n + 2)
    1 < Nat.gcd x y ∨ 1 < Nat.gcd x z ∨ 1 < Nat.gcd y z

/-- The lexicographically earliest admissible sequence contains every positive integer. -/
theorem main : ∃ a : ℕ+ → ℕ+, Admissible a ∧
    (∀ b : ℕ+ → ℕ+, Admissible b → toLex a ≤ toLex b) ∧
    Function.Surjective a := by
  sorry

end OMA.S_oeis_a338618

