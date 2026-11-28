import Mathlib

/-!
# Does independent sign symmetrization increase this logarithmic expectation?

Source: D_809, https://mathoverflow.net/questions/357953 (CC BY-SA 4.0).
Credit: @connoranderson.

The product measure samples independent copies of the same random variable.
A uniform average over all sign vectors implements independent symmetric signs.
Writing the number of coordinates as k+2 includes every arity in the question.
-/

namespace OMA.S_mo_357953
open Finset MeasureTheory

noncomputable def statistic {k : ℕ} (x : Fin (k+2) → ℝ) : ℝ :=
  let A := (∏ i, (1+x i)) + (∏ i, (1-x i))
  let B := 1 - x 0 * x ⟨1,by omega⟩
  A * Real.log A - (k+2:ℕ) * B * Real.log B

def signReal (b : Fin 2) : ℝ := if b = 0 then 1 else -1

noncomputable def original (k : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ w : Fin (k+2) → Ω, statistic (fun i => X (w i)) ∂Measure.pi (fun _ => P)

noncomputable def symmetrized (k : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  (∑ b : Fin (k+2) → Fin 2, ∫ w : Fin (k+2) → Ω,
    statistic (fun i => signReal (b i) * X (w i)) ∂Measure.pi (fun _ => P)) / (2:ℝ)^(k+2)

theorem main : ∀ (k : ℕ) (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ),
    Measurable X → (∀ᵐ w ∂P, X w ∈ Set.Ioo (-1:ℝ) 1) → (∫ w, X w ∂P)=0 →
    original k P X ≤ symmetrized k P X := by
  sorry

end OMA.S_mo_357953
