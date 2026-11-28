import Mathlib

/-!
# Hamiltonian approach to Einstein manifold theory

Source: https://mathoverflow.net/questions/473763
Credit: @Concretizzare

Draft statement for the two trajectory questions, using the connected,
boundaryless convention. The source leaves connectedness implicit; this
convention needs confirmation during statement review.

The curvature convention is `R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.
The connection is specified directly by the Koszul formula.
-/

noncomputable section

namespace OMA.S_mo_473763

open Bundle FiberBundle Set VectorField
open scoped BigOperators Bundle ContDiff Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]

abbrev Vector (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :=
  (x : M) → TangentSpace I x

section Metric

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The metric pairing of `∇_X Y` and `Z`, computed in terms of the metric. -/
def koszul (X Y Z : Vector I M) (q : M) : ℝ :=
  (mvfderiv I (fun p => inner ℝ (Y p) (Z p)) q (X q)
    + mvfderiv I (fun p => inner ℝ (Z p) (X p)) q (Y q)
    - mvfderiv I (fun p => inner ℝ (X p) (Y p)) q (Z q)
    - inner ℝ (Y q) (mlieBracket I X Z q)
    - inner ℝ (Z q) (mlieBracket I Y X q)
    + inner ℝ (X q) (mlieBracket I Z Y q)) / 2

/-- Recover the covariant derivative from the metric pairing in an orthonormal basis. -/
def connection (X Y : Vector I M) (q : M) : TangentSpace I q :=
  letI : FiniteDimensional ℝ (TangentSpace I q) := inferInstanceAs (FiniteDimensional ℝ E)
  let basis := stdOrthonormalBasis ℝ (TangentSpace I q)
  ∑ i, koszul I X Y (extend E (basis i)) q • basis i

def curvature (X Y Z : Vector I M) (q : M) : TangentSpace I q :=
  connection I X (connection I Y Z) q
    - connection I Y (connection I X Z) q
    - connection I (mlieBracket I X Y) Z q

/-- The trace of `w ↦ R(w,u)v`, evaluated in an orthonormal basis. -/
def ricci (q : M) (u v : TangentSpace I q) : ℝ :=
  letI : FiniteDimensional ℝ (TangentSpace I q) := inferInstanceAs (FiniteDimensional ℝ E)
  let basis := stdOrthonormalBasis ℝ (TangentSpace I q)
  ∑ i, inner ℝ (basis i) (curvature I (extend E (basis i)) (extend E u) (extend E v) q)

def einstein : Prop :=
  ∃ c : ℝ, ∀ (q : M) (u v : TangentSpace I q), ricci I q u v = c * inner ℝ u v

end Metric

section Hamiltonian

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

abbrev Phase (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E × (E →L[ℝ] ℝ)

abbrev Cotangent (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :=
  Bundle.TotalSpace (E →L[ℝ] ℝ) (fun q : M ↦ TangentSpace I q →L[ℝ] Bundle.Trivial M ℝ q)

abbrev cotangentModel := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)

/-! The metric identifies the punctured tangent and cotangent bundles. The
canonical form on the cotangent bundle pulls back to the form in the question. -/

def hamiltonian (z : Cotangent I M) : ℝ :=
  letI : FiniteDimensional ℝ (TangentSpace I z.1) := inferInstanceAs (FiniteDimensional ℝ E)
  letI := FiniteDimensional.complete ℝ (TangentSpace I z.1)
  let u := (InnerProductSpace.toDual ℝ (TangentSpace I z.1)).symm z.2
  ricci I z.1 u u / inner ℝ u u

/-- Contraction of the canonical form `-dθ` with the first vector. -/
def omega (v : Phase E) : Phase E →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ v.1).comp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] ℝ)) -
    v.2.comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ))

/-- The Hamiltonian equation in each cotangent chart, away from the zero section. -/
def obeysHamiltonianEquation (X : Vector (cotangentModel I) (Cotangent I M)) : Prop :=
  ∀ (a z : Cotangent I M), z.2 ≠ 0 → z ∈ (extChartAt (cotangentModel I) a).source →
    HasFDerivAt (hamiltonian I ∘ (extChartAt (cotangentModel I) a).symm)
      (omega (mfderiv (cotangentModel I) 𝓘(ℝ, Phase E)
        (extChartAt (cotangentModel I) a) z (X z)))
      (extChartAt (cotangentModel I) a z)

def isTrajectoryOn (X : Vector (cotangentModel I) (Cotangent I M))
    (γ : ℝ → Cotangent I M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, (γ t).2 ≠ 0 ∧ IsMIntegralCurveAt (I := cotangentModel I) γ X t

def periodicOrStationary (X : Vector (cotangentModel I) (Cotangent I M)) : Prop :=
  ∀ z, z.2 ≠ 0 → X z = 0 ∨
    ∃ T : ℝ, 0 < T ∧ ∃ γ : ℝ → Cotangent I M,
      γ 0 = z ∧ γ T = z ∧ isTrajectoryOn I X γ (Icc 0 T)

def compactOrbits (X : Vector (cotangentModel I) (Cotangent I M)) : Prop :=
  ∀ z, z.2 ≠ 0 → ∃ K : Set (Cotangent I M),
    IsCompact K ∧ K ⊆ {w | w.2 ≠ 0} ∧ z ∈ K ∧
    (∃ γ : ℝ → Cotangent I M, γ 0 = z ∧ isTrajectoryOn I X γ univ) ∧
    ∀ (γ : ℝ → Cotangent I M) (J : Set ℝ),
      IsOpen J → IsPreconnected J → 0 ∈ J → γ 0 = z → isTrajectoryOn I X γ J →
      MapsTo γ J K

end Hamiltonian

section Questions

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]

/-- The smooth Riemannian metric ranges over all metrics on the fixed manifold. -/
def admitsEinsteinMetric : Prop :=
  ∃ _g : RiemannianBundle (fun q : M ↦ TangentSpace I q),
    ∃ _ : IsContMDiffRiemannianBundle I ∞ E (fun q : M ↦ TangentSpace I q), einstein I (M := M)

def hasOrbitPropertyWithoutEinsteinMetric
    (orbitProperty : Vector (cotangentModel I) (Cotangent I M) → Prop) : Prop :=
  ¬ admitsEinsteinMetric I (M := M) ∧
    ∃ _g : RiemannianBundle (fun q : M ↦ TangentSpace I q),
      ∃ _ : IsContMDiffRiemannianBundle I ∞ E (fun q : M ↦ TangentSpace I q),
        ∃ X : Vector (cotangentModel I) (Cotangent I M),
          obeysHamiltonianEquation I X ∧ orbitProperty X

end Questions

universe u v w

/-- Existence for the periodic-or-stationary option, with the connected convention. -/
def periodicExample : Prop :=
  ∃ (F : Type u) (K : Type v) (N : Type w)
    (_ : NormedAddCommGroup F) (_ : NormedSpace ℝ F) (_ : FiniteDimensional ℝ F)
    (_ : TopologicalSpace K) (J : ModelWithCorners ℝ F K) (_ : J.Boundaryless)
    (_ : TopologicalSpace N) (_ : ChartedSpace K N) (_ : IsManifold J ∞ N)
    (_ : T2Space N) (_ : ConnectedSpace N),
      hasOrbitPropertyWithoutEinsteinMetric J (periodicOrStationary J (M := N))

/-- Existence for the compact-confinement option, with the same convention. -/
def compactExample : Prop :=
  ∃ (F : Type u) (K : Type v) (N : Type w)
    (_ : NormedAddCommGroup F) (_ : NormedSpace ℝ F) (_ : FiniteDimensional ℝ F)
    (_ : TopologicalSpace K) (J : ModelWithCorners ℝ F K) (_ : J.Boundaryless)
    (_ : TopologicalSpace N) (_ : ChartedSpace K N) (_ : IsManifold J ∞ N)
    (_ : T2Space N) (_ : ConnectedSpace N),
      hasOrbitPropertyWithoutEinsteinMetric J (compactOrbits J (M := N))

/-- The two existence questions on connected smooth Riemannian manifolds without boundary.
The final statement and its scope must be reviewed before the proof submission. -/
theorem main : ¬ periodicExample.{u, v, w} ∧ compactExample.{0, 0, 0} := by
  sorry

end OMA.S_mo_473763
