import Mathlib

/-!
# Distance between unitary and antiunitary operators

Source: jacaboul, https://mathoverflow.net/questions/442655 (CC BY-SA).
The source gives the universal square-root-of-two lower bound.
Credit: @connoranderson.

A nonnegative real number bounds the real operator norm of a pair's
difference exactly when the pointwise inequality in `radii` holds.
Every antiunitary is a unitary matrix followed, on its right, by coordinatewise
complex conjugation. The least attainable upper bound is the requested distance.
-/

namespace OMA.S_mo_442655
open Matrix

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
noncomputable def euclid {n : ℕ} (x : Fin n → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖
def radii (n : ℕ) : Set ℝ := {r | 0 ≤ r ∧
  ∃ U V : Matrix.unitaryGroup (Fin n) ℂ, ∀ x : Fin n → ℂ,
    euclid ((U : Mat n) *ᵥ x - (V : Mat n) *ᵥ star x) ≤ r * euclid x}

theorem main : ∀ n : ℕ, 0 < n →
    IsLeast (radii n) (if Even n then Real.sqrt 2 else 2) := by
  sorry
end OMA.S_mo_442655
