import Mathlib

/-!
# Relative Equilibria of Dumbbells Orbiting in a Planar Newtonian Gravitational System

Source: https://arxiv.org/abs/2307.01935 (J. Morey, 2023)
Credit: @eltociear

`main` states Theorem 12.2 of the source (Perpendicular Bisector Theorem for RE of a
Dumbbell and Rigid Planar Bodies), the geometric restriction on the location of
relative equilibria highlighted in the abstract: the source's extension of the
Conley–Moeckel Perpendicular Bisector Theorem (Theorem 12.1 of the source).

Theorem 12.2 of the source: Let a dumbbell r₁r₂ and one or more planar rigid bodies
B₂, …, Bₙ be in a planar RE. Then, if one of the two open cones determined by the
lines through r₁r₂ and its perpendicular bisector contains one or more rigid bodies,
the other open cone cannot be empty.

Conventions of this translation.
* Following Section 12 of the source, every rigid body is a discretized body: a
  finite nonempty set of point masses, all connected by massless rods, with a point
  mass body being trivially discretized, and a dumbbell the discretized body with
  exactly two point masses. The system is a finite type `ι` of point masses with a
  body assignment `bodyOf : ι → Fin n`, where `n ≥ 2` and body `0` is the dumbbell,
  consisting of exactly the two masses `d₁`, `d₂`. Masses `m : ι → ℝ` are positive,
  positions `r : ι → (Fin 2 → ℝ)` are pairwise distinct (no collisions), and `G > 0`
  is Newton's gravitational constant.
* A planar relative equilibrium (RE) is rendered by its standard characterization:
  in the centre-of-mass frame (`∑ i, m i • r i = 0`) the configuration can rotate
  rigidly about the centre of mass with a constant angular velocity `ω ≠ 0` as a
  solution of Newton's equations. For each rigid body this is the pair of conditions:
  the total gravitational force on the body equals `-ω²` times the body's first mass
  moment (so the body's centre of mass has the centripetal acceleration `-ω² r`),
  and the total gravitational torque about the body's own centre of mass is zero
  (no angular acceleration). The force on a point mass is the gravitational force
  from all other point masses; internal forces inside a body cancel in both
  conditions (Newton's third law, and internal gravity is central), as in the source.
* The two open cones of Section 12 of the source: the line through `r₁, r₂` and its
  perpendicular bisector form four quadrants; a cone is the hourglass union of two
  opposite quadrants, and an open cone is a cone minus the axes. Writing
  `s(x) = (x - mid) · (r₂ - r₁)` for the signed axial coordinate relative to the
  midpoint `mid` of the dumbbell and `t(x) = cross (r₂ - r₁) (x - mid)` for the
  perpendicular component, the two open cones are `{x | 0 < s(x) * t(x)}` and
  `{x | s(x) * t(x) < 0}`.
* A rigid body is contained in an open cone when all of its point masses lie in it,
  as in the source's proof (if the bodies B_k are all in one open cone, then for a
  RE either both cones are empty or both are occupied). The conclusion is stated for
  both cones, the source's: the other open cone cannot be empty.
-/

namespace OMA.S_arxiv_2307_01935

/-- Coordinate dot product in the plane. -/
def dot2 (u v : Fin 2 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1

/-- Scalar cross product (the z-component) in the plane. -/
def cross2 (u v : Fin 2 → ℝ) : ℝ := u 0 * v 1 - u 1 * v 0

/-- Euclidean distance in the plane. -/
noncomputable def euclidDist (u v : Fin 2 → ℝ) : ℝ := Real.sqrt ((u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2)

/-- The gravitational force exerted on point mass `i` by all the other point masses.
The `j = i` term vanishes on its own: its distance is `0`, so its coefficient is `0`. -/
noncomputable def gravForce {ι : Type} [Fintype ι] (m : ι → ℝ) (r : ι → (Fin 2 → ℝ)) (G : ℝ) (i : ι) :
    Fin 2 → ℝ :=
  ∑ j, (G * m j / euclidDist (r j) (r i) ^ 3) • (r j - r i)

/-- The point masses belonging to body `k`. -/
def bodyMasses {ι : Type} [Fintype ι] {n : ℕ} (bodyOf : ι → Fin n) (k : Fin n) : Finset ι :=
  Finset.univ.filter (fun i => bodyOf i = k)

/-- Total mass of body `k`. -/
def bodyMass {ι : Type} [Fintype ι] {n : ℕ} (bodyOf : ι → Fin n) (m : ι → ℝ) (k : Fin n) :
    ℝ :=
  ∑ i ∈ bodyMasses bodyOf k, m i

/-- Centre of mass of body `k`. -/
noncomputable def bodyCenter {ι : Type} [Fintype ι] {n : ℕ} (bodyOf : ι → Fin n) (m : ι → ℝ)
    (r : ι → (Fin 2 → ℝ)) (k : Fin n) : Fin 2 → ℝ :=
  (bodyMass bodyOf m k)⁻¹ • ∑ i ∈ bodyMasses bodyOf k, m i • r i

/-- Planar relative equilibrium: in the centre-of-mass frame the configuration
rotates rigidly with some constant angular velocity `ω ≠ 0`; for every body, the
total gravitational force gives its centre of mass the centripetal acceleration
`-ω² r`, and the total gravitational torque about its own centre of mass vanishes. -/
def IsRelativeEquilibrium {ι : Type} [Fintype ι] {n : ℕ} (bodyOf : ι → Fin n)
    (m : ι → ℝ) (r : ι → (Fin 2 → ℝ)) (G : ℝ) : Prop :=
  ∃ ω : ℝ, ω ≠ 0 ∧ (∑ i, m i • r i) = 0 ∧ ∀ k : Fin n,
    (∑ i ∈ bodyMasses bodyOf k, gravForce m r G i)
        = (-ω ^ 2) • ∑ i ∈ bodyMasses bodyOf k, m i • r i ∧
    (∑ i ∈ bodyMasses bodyOf k,
      cross2 (r i - bodyCenter bodyOf m r k) (gravForce m r G i)) = 0

/-- Midpoint of the dumbbell `r₁r₂`. -/
noncomputable def dumbbellMidpoint (r₁ r₂ : Fin 2 → ℝ) : Fin 2 → ℝ := (2 : ℝ)⁻¹ • (r₁ + r₂)

/-- Signed axial coordinate of `x` relative to the dumbbell: positive on the `r₂`
side of the perpendicular bisector, negative on the `r₁` side, zero on the bisector. -/
noncomputable def axialCoord (r₁ r₂ x : Fin 2 → ℝ) : ℝ := dot2 (x - dumbbellMidpoint r₁ r₂) (r₂ - r₁)

/-- Perpendicular component of `x` relative to the dumbbell line: zero exactly on
the line through `r₁` and `r₂`. -/
noncomputable def perpCoord (r₁ r₂ x : Fin 2 → ℝ) : ℝ := cross2 (r₂ - r₁) (x - dumbbellMidpoint r₁ r₂)

/-- The first open cone of the source: the hourglass union of the first and third
quadrants formed by the dumbbell line and its perpendicular bisector, axes removed. -/
def InFirstCone (r₁ r₂ x : Fin 2 → ℝ) : Prop := 0 < axialCoord r₁ r₂ x * perpCoord r₁ r₂ x

/-- The second open cone: the hourglass union of the second and fourth quadrants. -/
def InSecondCone (r₁ r₂ x : Fin 2 → ℝ) : Prop := axialCoord r₁ r₂ x * perpCoord r₁ r₂ x < 0

/-- Theorem 12.2 of the source (Perpendicular Bisector Theorem for RE of a Dumbbell
and Rigid Planar Bodies): if one of the two open cones determined by the dumbbell
and its perpendicular bisector contains one or more rigid bodies, the other open
cone cannot be empty; stated for both cones. -/
theorem main : ∀ (n : ℕ) [NeZero n] (ι : Type) [Fintype ι] (bodyOf : ι → Fin n) (m : ι → ℝ)
    (r : ι → (Fin 2 → ℝ)) (G : ℝ) (d₁ d₂ : ι),
    2 ≤ n → 0 < G → (∀ i, 0 < m i) → Function.Injective r →
    (∀ k, (bodyMasses bodyOf k).Nonempty) →
    bodyOf d₁ = 0 → bodyOf d₂ = 0 → d₁ ≠ d₂ →
    (∀ i, bodyOf i = 0 → i = d₁ ∨ i = d₂) →
    IsRelativeEquilibrium bodyOf m r G →
    ((∃ k : Fin n, k ≠ 0 ∧ ∀ i ∈ bodyMasses bodyOf k, InFirstCone (r d₁) (r d₂) (r i)) →
      (∃ k : Fin n, k ≠ 0 ∧ ∀ i ∈ bodyMasses bodyOf k, InSecondCone (r d₁) (r d₂) (r i))) ∧
    ((∃ k : Fin n, k ≠ 0 ∧ ∀ i ∈ bodyMasses bodyOf k, InSecondCone (r d₁) (r d₂) (r i)) →
      (∃ k : Fin n, k ≠ 0 ∧ ∀ i ∈ bodyMasses bodyOf k, InFirstCone (r d₁) (r d₂) (r i))) := by
  sorry

end OMA.S_arxiv_2307_01935
