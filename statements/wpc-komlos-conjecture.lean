import Mathlib

/-!
# Komlós conjecture

Source: https://en.wikipedia.org/wiki/Discrepancy_theory
Credit: @mgv27

There is an absolute constant K such that for all vectors v₁,…,vₙ in ℝᵐ of Euclidean norm
at most 1 there are signs ε₁,…,εₙ ∈ {−1,1} with ‖ε₁v₁ + … + εₙvₙ‖_∞ ≤ K. It implies the
Beck–Fiala conjecture; the best known bounds grow slowly with n (Banaszczyk's O(√log n) and
later improvements).

Formalization notes:
* Vectors live in `EuclideanSpace ℝ (Fin m)`, so `‖v i‖` is the Euclidean norm.
* The sup-norm bound is stated coordinatewise: every coordinate of `∑ εᵢ vᵢ` has absolute
  value at most `K`.
* `K` is chosen once, before `m`, `n` and the vectors.
-/

namespace OMA.S_wpc_komlos_conjecture

/-- `ε` is a sign vector: every entry is `1` or `-1`. -/
def IsSigns {n : ℕ} (ε : Fin n → ℝ) : Prop :=
  ∀ i, ε i = 1 ∨ ε i = -1

/-- Komlós conjecture. -/
theorem main : ∃ K : ℝ, ∀ (m n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)),
    (∀ i, ‖v i‖ ≤ 1) →
    ∃ ε : Fin n → ℝ, IsSigns ε ∧ ∀ j : Fin m, |∑ i, ε i * v i j| ≤ K := by
  sorry

end OMA.S_wpc_komlos_conjecture
