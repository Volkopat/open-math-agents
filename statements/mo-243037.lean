import Mathlib

/-!
# Orthogonally invariant measures on the infinite-dimensional Hilbert sphere

Source: ijon, https://mathoverflow.net/questions/243037 (CC BY-SA 3.0).
Credit: @connoranderson.

Counting measure answers the literal existence question. The open-set
conclusion rules out an invariant probability measure, the random-direction
interpretation clarified by the questioner. A symmetric law on an antipodal
pair is invariant under every orthogonal map preserving its unoriented line.
-/

namespace OMA.S_mo_243037

open MeasureTheory Metric Set
open scoped ENNReal

abbrev S (H : Type) [NormedAddCommGroup H] := sphere (0:H) 1

def act {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : H ≃ₗᵢ[ℝ] H)
    (x : S H) : S H := ⟨e x,mem_sphere_zero_iff_norm.mpr (e.norm_map _ |>.trans
      (mem_sphere_zero_iff_norm.mp x.property))⟩

def antipode {H : Type} [NormedAddCommGroup H] (x : S H) : S H :=
  ⟨-x.val,mem_sphere_zero_iff_norm.mpr ((norm_neg _).trans (mem_sphere_zero_iff_norm.mp x.property))⟩

noncomputable def lineLaw {H : Type} [NormedAddCommGroup H] [MeasurableSpace H] (x : S H) : Measure (S H) :=
  (2:ℝ≥0∞)⁻¹ • (Measure.dirac x + Measure.dirac (antipode x))

theorem main : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H], ¬ FiniteDimensional ℝ H →
    (∀ e : H ≃ₗᵢ[ℝ] H, (Measure.count : Measure (S H)).map (act e) = Measure.count) ∧
    (∀ μ : Measure (S H), μ ≠ 0 → (∀ e : H ≃ₗᵢ[ℝ] H, μ.map (act e) = μ) →
      ∀ U : Set (S H), IsOpen U → U.Nonempty → μ U = ⊤) ∧
    (∀ x : S H, IsProbabilityMeasure (lineLaw x) ∧
      ∀ e : H ≃ₗᵢ[ℝ] H, act e x=x ∨ act e x=antipode x → (lineLaw x).map (act e)=lineLaw x) := by
  sorry

end OMA.S_mo_243037
