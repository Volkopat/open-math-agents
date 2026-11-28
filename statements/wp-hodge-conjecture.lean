import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The rational Hodge conjecture

Source: https://en.wikipedia.org/wiki/Hodge_conjecture
Credit: @Hennyrick

We use the equivalent homological statement for a connected smooth projective
complex variety. The geometry, tangent-space type test, periods and supports
are defined below. No choice of cohomology theory or cycle-class map occurs
in the hypotheses. Every smooth projective variety admits a projective embedding.

For the type and periods, see P. Deligne, The Hodge Conjecture, pp. 45–46.
For the top homology of an algebraic support, see V. Ginzburg, Geometric
methods in the representation theory of Hecke algebras and quantum groups,
Proposition 1.1 (arXiv:math/9802004).
-/

namespace OMA.S_wp_hodge_conjecture

open MeasureTheory
open scoped BigOperators

/-- The ambient complex matrix space. The projective point of a nonzero homogeneous
vector is the Hermitian orthogonal projector onto the complex line that it spans. -/
abbrev HSpace (n : ℕ) := (Fin (n + 1) × Fin (n + 1)) → ℂ

noncomputable def projPt {n : ℕ} (z : Fin (n + 1) → ℂ) : HSpace n :=
  fun ij => z ij.1 * star (z ij.2) / (∑ j, z j * star (z j))

/-- A projective algebraic set is the common zero locus of homogeneous polynomials.
The vector 0 does not represent a point of projective space. -/
def ProjAlg (n : ℕ) (X : Set (HSpace n)) : Prop :=
  ∃ equations : Set (MvPolynomial (Fin (n + 1)) ℂ),
    (∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e) ∧
    ∀ x, x ∈ X ↔ ∃ z : Fin (n + 1) → ℂ, z ≠ 0 ∧ projPt z = x ∧
      ∀ f ∈ equations, MvPolynomial.eval z f = 0

/-- A projective algebraic set has complex dimension at most k precisely when
some k+1 hyperplanes have no common point on it (projective dimension theorem
and generic hyperplane sections). This includes empty supports. -/
def SmallSupport (n k : ℕ) (Y : Set (HSpace n)) : Prop :=
  ProjAlg n Y ∧
  ∃ L : Fin (k + 1) → Fin (n + 1) → ℂ,
    ∀ z : Fin (n + 1) → ℂ, z ≠ 0 → projPt z ∈ Y →
      ∃ j, (∑ i, L j i * z i) ≠ 0

abbrev HChartSpace (d : ℕ) := Fin d → ℂ

/-- Holomorphic homogeneous coordinates on an open subset of complex affine space. -/
def HolLiftInto {n d : ℕ} (X : Set (HSpace n)) (U : Set (HChartSpace d))
    (g : HChartSpace d → (Fin (n + 1) → ℂ)) : Prop :=
  IsOpen U ∧ DifferentiableOn ℂ g U ∧
    ∀ u ∈ U, g u ≠ 0 ∧ projPt (g u) ∈ X

/-- A chart is a complex immersion inducing a homeomorphism onto an open subset of X.
The inverse only needs to be continuous on that subset. Local lifts of genuine charts
exist by normalising one nonzero homogeneous coordinate. The rank and topology
conditions preclude singular or multiply covered parametrisations. -/
def SmoothProj (n d : ℕ) (X : Set (HSpace n)) : Prop :=
  ProjAlg n X ∧ IsConnected X ∧ ∀ x ∈ X,
    ∃ (U : Set (HChartSpace d)) (V : Set (HSpace n))
      (g : HChartSpace d → (Fin (n + 1) → ℂ)) (h : HSpace n → HChartSpace d),
      HolLiftInto X U g ∧ IsOpen V ∧ x ∈ V ∧
      (fun u => projPt (g u)) '' U = X ∩ V ∧
      ContinuousOn h (X ∩ V) ∧ (∀ u ∈ U, h (projPt (g u)) = u) ∧
      ∀ u ∈ U, Function.Injective (fderiv ℝ (fun t => projPt (g t)) u)

abbrev AmbientForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) :=
  E → E [⋀^Fin m]→L[ℝ] ℂ

/-- Differential forms on a closed embedded manifold extend smoothly to the ambient
space. Closedness is imposed only on tangent vectors. A form of total degree 2k
has type (a,b) exactly when rotation of all its tangent arguments by z on the unit
circle multiplies its value by z^a times the conjugate of z to the power b.
Holomorphic lifts are enough to test both conditions, since they include local charts. -/
def OffDiagonalTest {n : ℕ} (X : Set (HSpace n)) (d k : ℕ)
    (ω : AmbientForm (HSpace n) (2 * k)) : Prop :=
  (∀ r : ℕ, ContDiff ℝ r ω) ∧
  ∃ a b : ℕ, a + b = 2 * k ∧ a ≠ b ∧
    ∀ (U : Set (HChartSpace d)) (g : HChartSpace d → (Fin (n + 1) → ℂ)),
      HolLiftInto X U g → ∀ u ∈ U,
        let f := fun t => projPt (g t)
        let D := fderiv ℝ f u
        (∀ v : Fin (2 * k + 1) → HChartSpace d,
          extDeriv ω (f u) (fun j => D (v j)) = 0) ∧
        ∀ (z : ℂ), ‖z‖ = 1 → ∀ v : Fin (2 * k) → HChartSpace d,
          ω (f u) (fun j => D (z • v j)) =
            (z ^ a * (star z) ^ b) * ω (f u) (fun j => D (v j))

-- The affine integration coordinates omit barycentric coordinate zero.
abbrev Param (k : ℕ) := Fin k → ℝ

def stdSimplex (k : ℕ) : Set (Param k) :=
  {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}

abbrev BarySimplex (k : ℕ) := ↥(_root_.stdSimplex ℝ (Fin (k + 1)))

abbrev Simplex (k : ℕ) (E : Type*) [TopologicalSpace E] := C(BarySimplex k, E)

abbrev Chain (k : ℕ) (E : Type*) [TopologicalSpace E] := Simplex k E →₀ ℚ

def ChainIn {k : ℕ} {E : Type*} [TopologicalSpace E] (X : Set E) (c : Chain k E) : Prop :=
  ∀ s, c s ≠ 0 → ∀ t, s t ∈ X

-- Push barycentric weights along the unique order-preserving injection skipping i.
noncomputable def simplexFace {k : ℕ} {E : Type*} [TopologicalSpace E]
    (s : Simplex (k + 1) E) (i : Fin (k + 2)) : Simplex k E :=
  s.comp ⟨_root_.stdSimplex.map i.succAbove, _root_.stdSimplex.continuous_map i.succAbove⟩

noncomputable def boundary (k : ℕ) {E : Type*} [TopologicalSpace E] :
    Chain (k + 1) E →ₗ[ℚ] Chain k E :=
  Finsupp.linearCombination ℚ (fun s =>
    ∑ i : Fin (k + 2), Finsupp.single (simplexFace s i) ((-1 : ℚ) ^ i.val))

def IsCycle {E : Type*} [TopologicalSpace E] {k : ℕ} (c : Chain k E) : Prop :=
  match k, c with
  | 0, _ => True
  | j + 1, a => boundary j a = 0

def IsSmoothSimplex {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Simplex k E) : Prop :=
  ∃ g : Param k → E, (∀ r : ℕ, ContDiff ℝ r g) ∧
    ∀ t : BarySimplex k, g (fun i => t.val i.succ) = s t

def IsSmoothChain {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : Chain k E) : Prop :=
  ∀ s, c s ≠ 0 → IsSmoothSimplex s

noncomputable def simplexExtension {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Simplex k E) : Param k → E := by
  classical
  exact if h : IsSmoothSimplex s then Classical.choose h else fun _ => 0

-- Affine coordinates t_i are the barycentric coordinates at vertices 1,...,j.
-- The tangent vectors below are the oriented coordinate basis of the simplex.
noncomputable def simplexPeriod {n j : ℕ} (ω : AmbientForm (HSpace n) j)
    (s : Simplex j (HSpace n)) : ℂ :=
  let g := simplexExtension s
  ∫ t in stdSimplex j, ω (g t) (fun i => fderiv ℝ g t (Pi.single i (1 : ℝ)))

noncomputable def period {n j : ℕ} (ω : AmbientForm (HSpace n) j)
    (c : Chain j (HSpace n)) : ℂ :=
  c.sum fun s q => (q : ℂ) * simplexPeriod ω s

/-- Homological form of the rational Hodge conjecture. A rational degree 2k
cycle has diagonal Hodge type exactly when its periods against every closed
off-diagonal pure-type form vanish. Its Poincaré dual has type (d-k,d-k).
A representative supported on an algebraic set of dimension at most k is
equivalent to a rational sum of fundamental classes: the top homology of that
compact set is generated by its k-dimensional irreducible components.
The chain witnessing homology is required to lie in X. -/
theorem main :
    ∀ (n d : ℕ) (X : Set (HSpace n)), SmoothProj n d X →
    ∀ k : ℕ, k ≤ d →
    ∀ c : Chain (2 * k) (HSpace n), ChainIn X c → IsSmoothChain c → IsCycle c →
    (∀ ω : AmbientForm (HSpace n) (2 * k), OffDiagonalTest X d k ω → period ω c = 0) →
    ∃ Y : Set (HSpace n), Y ⊆ X ∧ SmallSupport n k Y ∧
      ∃ a : Chain (2 * k) (HSpace n), ChainIn Y a ∧ IsCycle a ∧
        ∃ b : Chain (2 * k + 1) (HSpace n), ChainIn X b ∧ boundary (2 * k) b = c - a := by
  sorry

end OMA.S_wp_hodge_conjecture
