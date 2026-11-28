import Mathlib

/-!
# The Thue–Morse product in the Flajolet–Martin constant

Source https://mathoverflow.net/questions/230288/is-the-flajolet-martin-constant-irrational-is-it-transcendental

The question asks whether the product alpha in the formula for the
Flajolet–Martin constant is irrational and whether it is transcendental.
See also Allouche, https://doi.org/10.5802/jtnb.906, Section 3.3.
-/

namespace OMA.S_mo_230288

open Filter
open scoped BigOperators Topology

def thueMorseSign (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ (Nat.digits 2 n).sum

/-- The first N factors in the original order, beginning at index one. -/
noncomputable def partialProduct (N : ℕ) : ℝ :=
  ∏ i ∈ Finset.range N,
    ((2 * ((i : ℝ) + 1)) / (2 * ((i : ℝ) + 1) + 1)) ^ thueMorseSign (i + 1)

theorem main :
    ∃ α : ℝ, Tendsto partialProduct atTop (𝓝 α) ∧
      Irrational α ∧ Transcendental ℚ α := by
  sorry

end OMA.S_mo_230288
