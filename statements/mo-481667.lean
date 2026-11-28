import Mathlib

/-!
# Is the fundamental solution of `Y' = A(t) Y` with symmetric `A(t)` positive?

Source: https://mathoverflow.net/questions/481667
Credit: @koolkao

Question (De vinci, MathOverflow 481667, 2024; CC BY-SA 4.0). Let `{A(t)}_{t ∈ [0,1]}` be
time-varying symmetric matrices in `ℝ^{d×d}` with `sup_t ‖A(t)‖_op ≤ a < ∞`, and let `Y_t` solve
`dY_t/dt = A(t) Y_t`, `Y_0 = I_d`. If the `A(t)` commute, `Y_t = exp(∫_0^t A)` is positive
definite. Without the commutation condition, is it still true that `uᵀ Y_t u > 0` (or maybe
`≥ 0`) for every unit vector `u` and every `t`?

`main` states the weaker reading `uᵀ Y_t u ≥ 0` (a disproof of it also disproves the strict one).
A disproof is a family `A`, a solution `Y`, a time `t ∈ [0, 1]` and a vector `u` with
`uᵀ Y_t u < 0`.

Translation choices:
* matrices are `Matrix (Fin d) (Fin d) ℝ`; symmetric means `(A t)ᵀ = A t`;
* the bound `sup_t ‖A(t)‖_op ≤ a` is stated entrywise, `|A t i j| ≤ a` for `t ∈ [0, 1]`
  (equivalent up to a constant depending on `d`, so the hypothesis "some finite bound" is the
  same);
* `Y` is a classical solution on `[0, 1]`: every entry `t ↦ Y t i j` has derivative
  `(A t * Y t) i j` within `[0, 1]` at every `t ∈ [0, 1]`, and `Y 0 = 1`; `A` is not required to
  be continuous;
* `uᵀ Y_t u` is `u ⬝ᵥ (Y t *ᵥ u)`, and "for every unit vector" is replaced by "for every vector"
  (the sign is invariant under scaling).
-/

namespace OMA.S_mo_481667

open Matrix

/-- For symmetric, bounded `A(t)`, the solution of `Y' = A(t) Y`, `Y(0) = I` satisfies
`uᵀ Y_t u ≥ 0` for all `t ∈ [0, 1]` and all `u`. -/
theorem main :
    ∀ (d : ℕ) (A Y : ℝ → Matrix (Fin d) (Fin d) ℝ),
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (A t)ᵀ = A t) →
      (∃ a : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j, |A t i j| ≤ a) →
      Y 0 = 1 →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
        HasDerivWithinAt (fun s => Y s i j) ((A t * Y t) i j) (Set.Icc 0 1) t) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u : Fin d → ℝ, 0 ≤ u ⬝ᵥ (Y t *ᵥ u) := by
  sorry

end OMA.S_mo_481667
