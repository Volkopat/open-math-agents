import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor

/-!
# The nearest-integer conjecture for OEIS A357291

Clark Kimberling's sequence counts subsets of {1,...,n} of size at least three
for which the sum of the two smallest elements is strictly less than the
largest element minus the second largest. Charles R. Greathouse IV proposed
the rounding formula on October 11, 2022.

Source: https://oeis.org/A357291
-/

namespace OMA.S_oeis_a357291

/-- The two smallest elements are u and v, and the largest is z. Every
remaining element w lies above v and satisfies u+v < z-w. The inequality
u+v < z-v also covers a three-element subset, whose penultimate element is v. -/
def Frame (s : Finset ℕ) (u v z : ℕ) : Prop :=
  0 < u ∧ u < v ∧ u + 2*v < z ∧ u ∈ s ∧ v ∈ s ∧ z ∈ s ∧
    ∀ w ∈ s, w = u ∨ w = v ∨ w = z ∨ (v < w ∧ u+v+w < z)

/-- A qualifying subset of {1,...,n}. -/
def Good (n : ℕ) (s : Finset ℕ) : Prop :=
  ∃ u v z, z ≤ n ∧ Frame s u v z

/-- The cardinality of the family of qualifying subsets. -/
noncomputable def literalCount (n : ℕ) : ℕ := Nat.card {s : Finset ℕ // Good n s}

theorem main : ∀ n : ℕ, (literalCount n : ℤ) =
    round ((2 : ℚ)^n / 21 - (n : ℚ)^2 / 12 + n / 6) := by
  sorry

end OMA.S_oeis_a357291
