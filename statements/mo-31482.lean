import Mathlib

/-!
# The 'sensitivity' of 2-colorings of the d-dimensional integer lattice

Source: https://mathoverflow.net/questions/31482
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Two points of `ℤ^d` are neighbours if they differ by `1` in exactly one coordinate. A
two-colouring `C` of `ℤ^d` is nontrivial if the origin is red but each of the `d` coordinate axes
contains a blue point. The sensitivity `s_x(C)` of `x` is the number of neighbours of `x` coloured
differently from `x`, and `s(C) = max_x s_x(C)`. The question asks for a lower bound on `s(C)` in
terms of `d`, for example `s(C) ≥ k √d` for a constant `k > 0`; `main` states this example bound
(the asker shows it would be optimal up to the constant).

Conventions:
* Colourings are `C : (Fin d → ℤ) → Bool` with `true` = red. The neighbours of `x` are
  `x ± eᵢ`, so `s_x(C)` counts pairs `(i, ±)`.
* `s(C) ≥ k √d` is stated as: some point `x` has `s_x(C) ≥ k √d`.
-/

namespace OMA.S_mo_31482

/-- The sensitivity of `x` under `C`: neighbours `x ± eᵢ` with a different colour. -/
def sens {d : ℕ} (C : (Fin d → ℤ) → Bool) (x : Fin d → ℤ) : ℕ :=
  (Finset.univ.filter fun p : Fin d × Bool =>
    C (x + Pi.single p.1 (if p.2 then 1 else -1)) ≠ C x).card

/-- `C` is nontrivial: the origin is red, and every axis has a blue point. -/
def Nontrivial' {d : ℕ} (C : (Fin d → ℤ) → Bool) : Prop :=
  C 0 = true ∧ ∀ i : Fin d, ∃ t : ℤ, C (Pi.single i t) = false

/-- There is `k > 0` with `s(C) ≥ k √d` for every nontrivial colouring of every `ℤ^d`. -/
theorem main : ∃ k : ℝ, 0 < k ∧ ∀ (d : ℕ) (C : (Fin d → ℤ) → Bool), Nontrivial' C →
    ∃ x : Fin d → ℤ, k * Real.sqrt d ≤ sens C x := by
  sorry

end OMA.S_mo_31482
