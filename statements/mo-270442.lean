import Mathlib

/-!
# a discrete operator begets even/odd polynomials

Source: https://mathoverflow.net/questions/270442
Credit: @zarnab222-dev

A nonempty partition is a decreasing list (allowing equality) of positive parts with sum n.
The falling factorial is evaluated in the integer polynomial ring. The first shift factor
divided by the forward difference is the sum of shifts from zero through the first part minus one.
Parity is tested by substituting -X, and coefficient inequalities are in the ordinary power basis.
-/

namespace OMA.S_mo_270442

open Polynomial

noncomputable def falling : ℕ → ℤ[X] → ℤ[X]
  | 0, _ => 1
  | n + 1, z => falling n z * (z - n)

noncomputable def differences : List ℕ → (ℤ[X] → ℤ[X]) → ℤ[X] → ℤ[X]
  | [], f, z => f z
  | a :: l, f, z => differences l f (z + a) - differences l f z

noncomputable def phi (n a : ℕ) (l : List ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range a, differences l (falling n) ((X : ℤ[X]) + (j : ℤ[X]))

theorem main : ∀ (n a : ℕ) (l : List ℕ), (a :: l).sum = n →
    (a :: l).Pairwise (· ≥ ·) → (∀ b ∈ a :: l, 0 < b) →
    let p := phi n a l
    (p.comp (-X) = p ∨ p.comp (-X) = -p) ∧ ∀ i, 0 ≤ p.coeff i := by
  sorry

end OMA.S_mo_270442
