import Mathlib

/-!
# Linear attainment of maximal correlation with one Gaussian marginal

In the centered real L² space of the joint distribution, take the two subspaces
of functions of each coordinate. A pair of normalized linear coordinates
attains maximal correlation exactly when each is orthogonal to the nonlinear
residuals from the opposite subspace, and the correlation of the two residual
subspaces is bounded by the linear value. This criterion applies to either sign
of the covariance, including zero.

For an explicit absolutely continuous joint law, let Z,W be independent
standard normals. Use (Z,Z+W) with weight 1/4, (2Z,Z+W) with weight 1/2, and
independent N(0,1), N(0,2) coordinates with weight 1/4. The maximal squared
correlation equals its positive squared Pearson correlation, 5/16. Its first
marginal is not Gaussian, while its second is exactly Gaussian.

Source: math-Student, https://mathoverflow.net/questions/228204 (CC BY-SA 3.0).
Credit: @connoranderson (agent: Codex)
-/
namespace OMA.S_mo_228204
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal NNReal
def bounded {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (U V : Submodule ℝ H) (r : ℝ) : Prop :=
  ∀ u ∈ U, ∀ v ∈ V, ⟪u,v⟫^2 ≤ r^2 * ⟪u,u⟫ * ⟪v,v⟫
noncomputable abbrev γ : Measure ℝ := gaussianReal 0 1
noncomputable abbrev ν : Measure ℝ := gaussianReal 0 2
noncomputable def coupled (s : ℝ) : Measure (ℝ×ℝ) :=
  (γ.prod γ).map (fun p : ℝ×ℝ => (s*p.1,p.1+p.2))
noncomputable def joint : Measure (ℝ×ℝ) :=
  ((1:ℝ≥0∞)/4) • coupled 1 + ((1:ℝ≥0∞)/2) • coupled 2 + ((1:ℝ≥0∞)/4) • (γ.prod ν)
noncomputable def μX : Measure ℝ := ((1:ℝ≥0∞)/2) • γ + ((1:ℝ≥0∞)/2) • gaussianReal 0 4
def centered (μ : Measure ℝ) (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ MemLp f 2 μ ∧ (∫ x,f x ∂μ)=0
/-- Squared Pearson correlation of centered transformations of the coordinates. -/
noncomputable def squaredCorrelation (f g : ℝ→ℝ) : ℝ :=
  (∫ p,f p.1*g p.2 ∂joint)^2 / ((∫ x,(f x)^2 ∂μX)*(∫ y,(g y)^2 ∂ν))
def attainable : Set ℝ := {r | ∃ f g : ℝ→ℝ, centered μX f ∧ centered ν g ∧
  0 < (∫ x,(f x)^2 ∂μX) ∧ 0 < (∫ y,(g y)^2 ∂ν) ∧ squaredCorrelation f g=r}
theorem main :
    (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (U V : Submodule ℝ H)
        (x y : H), x ∈ U → y ∈ V → ⟪x,x⟫=1 → ⟪y,y⟫=1 →
      (bounded U V ⟪x,y⟫ ↔
        (∀ u ∈ U, ⟪u,x⟫=0 → ⟪u,y⟫=0) ∧ (∀ v ∈ V, ⟪v,y⟫=0 → ⟪x,v⟫=0) ∧
        ∀ u ∈ U, ∀ v ∈ V, ⟪u,x⟫=0 → ⟪v,y⟫=0 →
          ⟪u,v⟫^2 ≤ ⟪x,y⟫^2 * ⟪u,u⟫ * ⟪v,v⟫)) ∧
    IsProbabilityMeasure joint ∧ joint ≪ volume ∧ joint.map Prod.fst = μX ∧ joint.map Prod.snd = ν ∧
    (∀ (m : ℝ) (v : ℝ≥0), μX ≠ gaussianReal m v) ∧
    centered μX id ∧ centered ν id ∧
    (∫ x,x^2 ∂μX)=5/2 ∧ (∫ y,y^2 ∂ν)=2 ∧ (∫ p,p.1*p.2 ∂joint)=5/4 ∧
    squaredCorrelation id id=5/16 ∧ IsGreatest attainable (5/16) := by
  sorry
end OMA.S_mo_228204
