import Mathlib

/-!
# Zeros of complex polynomials uniformly close in the unit disk

Source: MikeG, https://mathoverflow.net/questions/486714 (CC BY-SA 4.0).
Credit: @connoranderson.

The question asks whether angular projections must be close. Even the
normalized root-counting measures can stay separated by the continuous
angular test function that takes the absolute imaginary part on the unit
circle. Polynomial roots below are counted with multiplicity.
-/

namespace OMA.S_mo_486714

open Polynomial

noncomputable def angular (z : ℂ) : ℝ := |z.im| / ‖z‖

noncomputable def angularMean (P : ℂ[X]) : ℝ :=
  (P.roots.map angular).sum / P.natDegree

theorem main : ∃ f g : ℕ → ℂ[X],
    (∀ n, (f n).Monic ∧ (g n).Monic ∧ (f n).natDegree=n ∧ (g n).natDegree=n) ∧
    (∀ n z, (f n).IsRoot z ∨ (g n).IsRoot z → 1 ≤ ‖z‖) ∧
    (∀ r : ℝ, 0<r → r<1 → ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, ∀ z : ℂ,
      ‖z‖ ≤ r → ‖(f n).eval z - (g n).eval z‖ < ε) ∧
    ∃ δ : ℝ, 0<δ ∧ ∀ N : ℕ, ∃ n ≥ N,
      δ ≤ |angularMean (f n) - angularMean (g n)| := by
  sorry

end OMA.S_mo_486714
