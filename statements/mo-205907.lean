import Mathlib

/-!
# Minimum degree for a polynomial close to one on a prescribed interval

Source: Turbo, https://mathoverflow.net/questions/205907 (CC BY-SA 3.0).
Credit: @connoranderson.

The degree budget is sufficient exactly when it reaches the displayed ceiling.
-/

namespace OMA.S_mo_205907

open Polynomial

theorem main : ∀ a : ℝ, 0<a → a<1 → ∀ d : ℕ,
    (∃ f : ℝ[X], f.natDegree ≤ d ∧ f.eval 0 = 0 ∧
      ∀ x ∈ Set.Icc (1-a) (1+a), f.eval x ∈ Set.Icc (1-a/2) (1+a/2)) ↔
    ⌈Real.arcosh (2/a) / Real.arcosh (1/a)⌉₊ ≤ d := by
  sorry

end OMA.S_mo_205907
