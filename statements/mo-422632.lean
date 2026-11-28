import Mathlib

/-!
# The sublinear Jensen inequality for vector integrals

Nik Bren asks whether a sublinear functional can violate Jensen's inequality
for vector integrals over a measure that is not sigma-finite. A closed
epigraph cone gives the inequality for every Pettis integral and hence every
Bochner integral, allowing the functional to take the value +∞. The separating
functional argument was suggested by Jochen Wengenroth in the source discussion.
Without the closedness hypothesis an everywhere finite linear functional on
real ℓ² can violate Jensen even for a Bochner integrable random vector whose
image under the functional is identically zero.

Source: Nik Bren, https://mathoverflow.net/questions/422632 (CC BY-SA 4.0).
Credit: @connoranderson (agent: Codex)
-/

namespace OMA.S_mo_422632
open MeasureTheory

def PettisValue {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (X : Ω → E) (z : E) : Prop :=
  ∀ L : E →L[ℝ] ℝ, Integrable (fun x => L (X x)) μ ∧ L z = ∫ x, L (X x) ∂μ

def EpigraphCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → WithTop ℝ) : Prop :=
  ∃ C : ProperCone ℝ (E × ℝ), ∀ x r, (x,r) ∈ C ↔ f x ≤ (r : WithTop ℝ)

abbrev H := lp (fun _ : ℕ => ℝ) 2

theorem main :
    (∀ (Ω E : Type) [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
      (μ : Measure Ω) (X : Ω → E) (z : E) (f : E → WithTop ℝ) (g : Ω → ℝ),
      EpigraphCone f → PettisValue μ X z → Integrable g μ →
      (∀ᵐ ω ∂μ, f (X ω) ≤ (g ω : WithTop ℝ)) → f z ≤ ((∫ ω, g ω ∂μ : ℝ) : WithTop ℝ)) ∧
    (∀ (Ω E : Type) [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] (μ : Measure Ω) (X : Ω → E), Integrable X μ →
      PettisValue μ X (∫ ω, X ω ∂μ)) ∧
    (∃ (μ : Measure ℕ) (X : ℕ → H) (F : H →ₗ[ℝ] ℝ),
      ¬SigmaFinite μ ∧ Integrable X μ ∧ (∀ n, F (X n) = 0) ∧
      F (∫ n, X n ∂μ) = 1 ∧ (∫ n, F (X n) ∂μ) < F (∫ n, X n ∂μ)) := by
  sorry
end OMA.S_mo_422632
