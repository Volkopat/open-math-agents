import Mathlib

/-!
# MathOverflow 481044

Source: https://mathoverflow.net/questions/481044
-/

namespace OMA.S_mo_481044

open Finset

noncomputable def partialSpace {d : ℕ} (u : ℝ → (Fin d → ℝ) → Fin d → ℝ)
    (t : ℝ) (x : Fin d → ℝ) (i j : Fin d) : ℝ :=
  deriv (fun r => u t (Function.update x j r) i) (x j)

def pressurelessEuler {d : ℕ} (u : ℝ → (Fin d → ℝ) → Fin d → ℝ) : Prop :=
  (∀ i, ContDiff ℝ ⊤ (fun p : ℝ × (Fin d → ℝ) => u p.1 p.2 i)) ∧
    (∀ t x (k : Fin d → ℤ), u t (fun j => x j + k j) = u t x) ∧
    (∀ t x i, deriv (fun s => u s x i) t +
      (∑ j, u t x j * partialSpace u t x i j) = 0) ∧
    (∀ t x, (∑ i, partialSpace u t x i i) = 0) ∧
    (∃ t x i, deriv (fun s => u s x i) t ≠ 0)

theorem main : ∀ d : ℕ, 2 ≤ d →
    ∃ u : ℝ → (Fin d → ℝ) → Fin d → ℝ, pressurelessEuler u := by
  sorry

end OMA.S_mo_481044
