import Mathlib

/-!
# Side ratios of two random triangles

Three independent uniform points on a circle determine an inscribed triangle
and a triangle bounded by their three tangent lines. We compare the joint laws
of the three side lengths divided by their perimeter, which records all their
ratios. The side opposite a sampled vertex in the inscribed triangle corresponds
to the side on that vertex's tangent. Exchangeability also gives the random
ordering in the question. Similarities allow the unit circle in the complex plane.

For unit complex numbers u and v, the point 2uv/(u+v) is the intersection of
their tangent lines whenever u and v are distinct and non-antipodal. Parallel
lines and degenerate triangles are assigned the zero shape on their null events.

Source: https://math.stackexchange.com/questions/4893052 (CC BY-SA 4.0)
Credit: @connoranderson
-/

namespace OMA.S_mse_4893052
open MeasureTheory
noncomputable section

scoped instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
scoped instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

abbrev Sample := Fin 3 → Circle
abbrev Shape := ℝ × ℝ × ℝ

def ratios (a b c : ℝ) : Shape :=
  if a*b*c=0 then 0 else (a/(a+b+c), b/(a+b+c), c/(a+b+c))

def chord (u v : Circle) : ℝ := ‖(u:ℂ)-v‖

def inscribed (z : Sample) : Shape :=
  ratios (chord (z 1) (z 2)) (chord (z 2) (z 0)) (chord (z 0) (z 1))

def meetTangents (u v : Circle) : ℂ := 2*(u:ℂ)*v/(u+v:ℂ)

def tangentSide (u v w : Circle) : ℝ := ‖meetTangents u v - meetTangents u w‖

def denominator (u v w : Circle) : ℝ := ‖(u:ℂ)+v‖*‖(v:ℂ)+w‖*‖(w:ℂ)+u‖

def tangential (z : Sample) : Shape :=
  if denominator (z 0) (z 1) (z 2)=0 then 0 else
    ratios (tangentSide (z 0) (z 1) (z 2)) (tangentSide (z 1) (z 2) (z 0))
      (tangentSide (z 2) (z 0) (z 1))

theorem main : ∀ (μ : Measure Circle) [μ.IsHaarMeasure] [IsProbabilityMeasure μ],
    Measure.map inscribed (Measure.pi fun _ : Fin 3 => μ) =
      Measure.map tangential (Measure.pi fun _ : Fin 3 => μ) := by
  sorry

end
end OMA.S_mse_4893052
