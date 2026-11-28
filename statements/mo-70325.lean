import Mathlib

/-!
# Maximal parallelotopes anchored at the vertex of a truncated circular cone

Source: alext87, https://mathoverflow.net/questions/70325 (CC BY-SA 3.0).
Credit: @connoranderson.

Use coordinates with axis (1,...,1). The plane sum xᵢ=1 is at distance
1/√n from the origin, and the circular base in that plane has radius
√((n−1)/n). Every nondegenerate truncated right circular cone of dimension
at least two is a linear image of this normalized one, by rotation and
independent positive scalings along the axis and its orthogonal complement.

The vectors eᵢ/n span a maximum-volume anchored parallelotope. Its
normalized volume is n⁻ⁿ. The cone-volume formula therefore gives the exact
volume fraction, independently of aperture and height. The last inequality
also records a direct lower bound in terms of the unit n-ball volume.
-/

namespace OMA.S_mo_70325
open MeasureTheory
open scoped ENNReal
abbrev X (n : ℕ) := Fin n → ℝ
def height {n : ℕ} (x : X n) : ℝ := ∑ i,x i
def cone (n : ℕ) : Set (X n) := {x | 0 ≤ height x ∧ height x ≤ 1 ∧ ∑ i,(x i)^2 ≤ (height x)^2}
noncomputable def edges (n : ℕ) (i : Fin n) : X n := Pi.single i ((n:ℝ)⁻¹)
noncomputable def ballVolume (n : ℕ) : ℝ :=
  (2*Real.Gamma (1/2+1))^n / Real.Gamma ((n:ℝ)/2+1)

theorem main :
    (∀ n : ℕ, 2 ≤ n → volume.real (cone n) =
      (volume : Measure (EuclideanSpace ℝ (Fin (n-1)))).real (Metric.ball 0 1) *
      (Real.sqrt (((n-1 : ℕ) : ℝ)/(n:ℝ)))^(n-1) / ((n:ℝ)*Real.sqrt n)) ∧
    (∀ n : ℕ, volume (parallelepiped (edges n)) = ENNReal.ofReal ((n:ℝ)⁻¹^n)) ∧
    ∀ n : ℕ, 0<n → ∀ L : X n ≃ₗ[ℝ] X n,
      parallelepiped (L ∘ edges n) ⊆ L '' cone n ∧
      (∀ v : Fin n → X n, parallelepiped v ⊆ L '' cone n →
        volume (parallelepiped v) ≤ volume (parallelepiped (L ∘ edges n))) ∧
      ENNReal.ofReal (((n:ℝ)⁻¹^n)/ballVolume n) * volume (L '' cone n) ≤
        volume (parallelepiped (L ∘ edges n)) := by
  sorry
end OMA.S_mo_70325
