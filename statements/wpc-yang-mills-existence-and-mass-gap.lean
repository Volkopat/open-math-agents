import Mathlib

-- SPDX-License-Identifier: Apache-2.0

/-!
# Yang–Mills existence and mass gap

Source: Jaffe and Witten, *Quantum Yang–Mills Theory*, §4,
https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf
Credit: @justusklocke-cloud

This statement uses a Wilson lattice continuum limit for the gauge dynamics and
a Wightman reconstruction of a selected phase. The joint energy–momentum
spectral measure gives the spectral projection of its time-translation generator.
A nonzero projection in a bounded positive-energy interval expresses the finite
mass requirement.

The gauge, Wightman, Wilson, and continuum hierarchy definitions are adapted from
OpenAI-YM-20261028, commit 3456e5e, Apache-2.0. The adaptation changes the
namespace and instance declarations, uses one infinite-volume subsequence for
existence, and adds the spectral mass-gap condition to the selected theory.
The curvature-jet coordinate definitions are adapted from
OpenAI-YM-20261104, commit c1bb5a5566b2bad9d593980d470439f815895317, Apache-2.0.
See https://github.com/yang-mills-group/OpenAI-YM-20261104/tree/c1bb5a5566b2bad9d593980d470439f815895317
and https://github.com/yang-mills-group/OpenAI-YM-20261028/tree/3456e5e
and the November assessment at
https://github.com/yang-mills-group/YM/blob/main/docs/assessment-1.pdf.
-/

namespace OMA.S_wpc_yang_mills_existence_and_mass_gap


/-! Public gauge and Wightman definitions adapted from an earlier challenge,
commit eea94292e31734d46498be7836d7e8fa50ca8cd2. The symmetry
coordinates cover every proper orthochronous Lorentz transformation and
translation. Their affine action fixes the transformation of test functions. -/

noncomputable section

namespace YangMills

open MeasureTheory Set Function
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius

/-! ## Compact simple matrix gauge groups -/

/-- The fixed faithful unitary representation used to describe a gauge
group. -/
abbrev UnitaryRepresentation (n : ℕ) := Matrix.unitaryGroup (Fin (n + 1)) ℂ

/-- A compact matrix gauge group together with its one-parameter Lie
algebra.  The last field prevents the Lie algebra from being arbitrary: it
consists exactly of the matrices whose exponentials stay in the group. -/
structure GaugeGroup where
  n : ℕ
  image : Subgroup (UnitaryRepresentation n)
  imageClosed : IsClosed (image : Set (UnitaryRepresentation n))
  lieAlgebra : Submodule ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  generates : ∀ X,
    X ∈ lieAlgebra ↔
      ∀ t : ℝ, NormedSpace.exp (t • X) ∈
        Set.range (fun u : image ↦ (u.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))

namespace GaugeGroup

/-- Real simplicity of the Lie algebra, including the nonabelian
condition. -/
def IsSimple (gauge : GaugeGroup) : Prop :=
  (∃ X ∈ gauge.lieAlgebra, ∃ Y ∈ gauge.lieAlgebra,
    X * Y - Y * X ≠ 0) ∧
  ∀ ideal : Submodule ℝ (Matrix (Fin (gauge.n + 1)) (Fin (gauge.n + 1)) ℂ),
    ideal ≤ gauge.lieAlgebra →
    (∀ X ∈ gauge.lieAlgebra, ∀ Y ∈ ideal, X * Y - Y * X ∈ ideal) →
    ideal = ⊥ ∨ ideal = gauge.lieAlgebra

end GaugeGroup

/-! ## Spacetime and test functions -/

abbrev Axis := Fin 4
abbrev SpaceAxis := Fin 3
abbrev timeAxis : Axis := Fin.last 3
abbrev Spacetime := EuclideanSpace ℝ Axis
abbrev Space := EuclideanSpace ℝ SpaceAxis

def time (x : Spacetime) : ℝ := x timeAxis

def spatial (x : Spacetime) : Space :=
  WithLp.toLp 2 fun i ↦ x i.castSucc

/-- The closed forward light cone in the convention where time is the final
coordinate. -/
def forwardCone : Set Spacetime := {x | ‖spatial x‖ ≤ time x}

def minkowskiSquare (x : Spacetime) : ℝ := time x ^ 2 - ‖spatial x‖ ^ 2

def spacelike : Set Spacetime := {x | minkowskiSquare x < 0}

abbrev TestFunction := SchwartzMap Spacetime ℂ

/-- Pointwise complex conjugation of a Schwartz test function. -/
def conjugateTest : TestFunction →L[ℝ] TestFunction :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

/-! ## Basic quantum-field structures -/

/-- A bundled complex Hilbert space. -/
structure HilbertSpace where
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℂ carrier]
  [completeSpace : CompleteSpace carrier]

instance (H : HilbertSpace) : NormedAddCommGroup H.carrier := H.normedAddCommGroup
instance (H : HilbertSpace) : InnerProductSpace ℂ H.carrier := H.innerProductSpace
instance (H : HilbertSpace) : CompleteSpace H.carrier := H.completeSpace

namespace HilbertSpace

abbrev Operator (H : HilbertSpace) := H.carrier →L[ℂ] H.carrier

end HilbertSpace

/-- A bundled complex vector space of field labels. -/
structure FieldLabels where
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]

instance (L : FieldLabels) : AddCommGroup L.carrier := L.addCommGroup
instance (L : FieldLabels) : Module ℂ L.carrier := L.module

/-- Operator-valued tempered fields on one common invariant domain. -/
structure FieldSystem (H : HilbertSpace) (Labels : FieldLabels) where
  domain : Submodule ℂ H.carrier
  vacuum : domain
  field : Labels.carrier →ₗ[ℂ]
    TestFunction →ₗ[ℂ] (domain →ₗ[ℂ] domain)

namespace FieldSystem

variable {H : HilbertSpace} {Labels : FieldLabels}

def vector (fields : FieldSystem H Labels) :
    List (Labels.carrier × TestFunction) → fields.domain
  | [] => fields.vacuum
  | letter :: word => fields.field letter.1 letter.2 (fields.vector word)

/-- The vacuum expectation of an ordered product of smeared fields. -/
def vacuumExpectation (fields : FieldSystem H Labels) {n : ℕ}
    (labels : Fin n → Labels.carrier) (tests : Fin n → TestFunction) : ℂ :=
  inner ℂ fields.vacuum.1
    (fields.vector (List.ofFn fun i ↦ (labels i, tests i))).1

/-- W1's common-domain, temperedness, and cyclic-vacuum requirements. -/
structure DomainAxioms (fields : FieldSystem H Labels) : Prop where
  normalizedVacuum : ‖fields.vacuum.1‖ = 1
  denseDomain : Dense (fields.domain : Set H.carrier)
  cyclicVacuum : fields.domain =
    Submodule.span ℂ (Set.range fun word ↦ (fields.vector word).1)
  tempered (label : Labels.carrier) (state : fields.domain) :
    Continuous fun test ↦ (fields.field label test state).1

/-- The smeared adjoint identity on the common domain. -/
def AdjointAxiom (fields : FieldSystem H Labels)
    (adjointLabel : Labels.carrier →ₛₗ[starRingEnd ℂ] Labels.carrier) : Prop :=
  ∀ label test (left right : fields.domain),
    inner ℂ (fields.field label test left).1 right.1 =
      inner ℂ left.1
        (fields.field (adjointLabel label) (conjugateTest test) right).1

/-- Two test functions are causally disjoint when every difference of
points in their supports is spacelike. -/
def SpacelikeSeparated (left right : TestFunction) : Prop :=
  ∀ x ∈ tsupport left, ∀ y ∈ tsupport right, x - y ∈ spacelike

/-- W3's local commutativity condition. -/
def LocalCommutativity (fields : FieldSystem H Labels) : Prop :=
  ∀ leftLabel rightLabel leftTest rightTest,
    SpacelikeSeparated leftTest rightTest →
    ∀ state : fields.domain,
      fields.field leftLabel leftTest
          (fields.field rightLabel rightTest state) =
        fields.field rightLabel rightTest
          (fields.field leftLabel leftTest state)

/-- Each nonzero label has a nonzero smeared field operator. -/
def Faithful (fields : FieldSystem H Labels) : Prop :=
  ∀ label : Labels.carrier, label ≠ 0 →
    ∃ test : TestFunction, fields.field label test ≠ 0

end FieldSystem

/-! ## Translations, spectrum, and Poincaré covariance -/

/-- A strongly continuous unitary representation of spacetime
translations. -/
structure TranslationAction (H : HilbertSpace) where
  operator : Spacetime → H.Operator
  identity : operator 0 = ContinuousLinearMap.id ℂ _
  add (x y : Spacetime) :
    (operator x).comp (operator y) = operator (x + y)
  unitary (x : Spacetime) (state : H.carrier) :
    ‖operator x state‖ = ‖state‖
  stronglyContinuous (state : H.carrier) :
    Continuous fun x ↦ operator x state

/-- A projection-valued joint energy–momentum measure. -/
structure EnergyMomentumMeasure (H : HilbertSpace) where
  projection : Set Spacetime → H.Operator
  empty : projection ∅ = 0
  univ : projection Set.univ = ContinuousLinearMap.id ℂ _
  intersection {left right : Set Spacetime} :
    MeasurableSet left → MeasurableSet right →
      (projection left).comp (projection right) = projection (left ∩ right)
  selfAdjoint {region : Set Spacetime} :
    MeasurableSet region →
      (projection region).adjoint = projection region
  countablyAdditive (regions : ℕ → Set Spacetime)
      (measurable : ∀ i, MeasurableSet (regions i))
      (disjoint : Pairwise (Disjoint on regions)) (state : H.carrier) :
    HasSum (fun i ↦ projection (regions i) state)
      (projection (⋃ i, regions i) state)
  diagonal : H.carrier → Measure Spacetime
  finite (state : H.carrier) : IsFiniteMeasure (diagonal state)
  diagonalIdentity {region : Set Spacetime} (measurable : MeasurableSet region)
      (state : H.carrier) :
    ↑((diagonal state).real region) =
      inner ℂ state (projection region state)

namespace EnergyMomentumMeasure

instance {H : HilbertSpace} (E : EnergyMomentumMeasure H) (state : H.carrier) :
    IsFiniteMeasure (E.diagonal state) := E.finite state

end EnergyMomentumMeasure

/-- Proper, time-orientation-preserving linear transformations of Minkowski space. -/
abbrev ProperLorentz := {g : (Spacetime →L[ℝ] Spacetime)ˣ //
  LinearMap.det g.val.toLinearMap = 1 ∧
  (∀ x, minkowskiSquare (g.val x) = minkowskiSquare x) ∧
  (∀ x, g.val x ∈ forwardCone ↔ x ∈ forwardCone)}

/-- Standard coordinates on the full proper orthochronous Poincaré group. -/
abbrev PoincareCoordinates := ProperLorentz × Spacetime

/-- An action in any homeomorphic coordinate system, with its group law and
pullback of tests fixed by the ordinary affine action on spacetime. -/
structure PoincareAction (H : HilbertSpace) (Labels : FieldLabels) where
  Symmetry : Type
  [one : One Symmetry]
  [mul : Mul Symmetry]
  [topology : TopologicalSpace Symmetry]
  onStates : Symmetry → H.Operator
  onLabels : Symmetry → Labels.carrier ≃ₗ[ℂ] Labels.carrier
  onTests : Symmetry → TestFunction → TestFunction
  pureTranslation : Spacetime → Symmetry
  identity : onStates 1 = ContinuousLinearMap.id ℂ _
  composition (g h : Symmetry) :
    onStates (g * h) = (onStates g).comp (onStates h)
  unitary (g : Symmetry) (state : H.carrier) :
    ‖onStates g state‖ = ‖state‖
  stronglyContinuous (state : H.carrier) :
    Continuous fun g ↦ onStates g state
  coordinates : Symmetry ≃ₜ PoincareCoordinates
  identityCoordinates : (coordinates 1).1.val = 1 ∧ (coordinates 1).2 = 0
  productCoordinates (g h : Symmetry) :
    (coordinates (g * h)).1.val = (coordinates g).1.val * (coordinates h).1.val ∧
    (coordinates (g * h)).2 = (coordinates g).1.val.val (coordinates h).2 + (coordinates g).2
  translationCoordinates (x : Spacetime) :
    (coordinates (pureTranslation x)).1.val = 1 ∧ (coordinates (pureTranslation x)).2 = x
  pullback (g : Symmetry) (f : TestFunction) (x : Spacetime) :
    onTests g f x = f (((coordinates g).1.val⁻¹).val (x - (coordinates g).2))
  translationZero : pureTranslation 0 = 1
  translationAdd (x y : Spacetime) :
    pureTranslation (x + y) = pureTranslation x * pureTranslation y

instance {H : HilbertSpace} {L : FieldLabels} (A : PoincareAction H L) : One A.Symmetry := A.one
instance {H : HilbertSpace} {L : FieldLabels} (A : PoincareAction H L) : Mul A.Symmetry := A.mul
instance {H : HilbertSpace} {L : FieldLabels} (A : PoincareAction H L) :
    TopologicalSpace A.Symmetry := A.topology

/-! ## Wightman axioms W0–W3 -/

/-- The observable data of a relativistic quantum field theory. -/
structure WightmanTheory (H : HilbertSpace) (Labels : FieldLabels) where
  fields : FieldSystem H Labels
  adjointLabel : Labels.carrier →ₛₗ[starRingEnd ℂ] Labels.carrier
  translations : TranslationAction H
  energyMomentum : EnergyMomentumMeasure H
  poincare : PoincareAction H Labels
  translationCompatibility (x : Spacetime) :
    poincare.onStates (poincare.pureTranslation x) = translations.operator x

namespace WightmanTheory

variable {H : HilbertSpace} {Labels : FieldLabels}

/-- W0: Hilbert-space covariance, the spectrum condition, and uniqueness of
the invariant vacuum. -/
structure W0 (theory : WightmanTheory H Labels) : Prop where
  spectralRepresentation : ∀ state : H.carrier, ∀ momentum : Spacetime,
    charFun (theory.energyMomentum.diagonal state) momentum =
      inner ℂ state (theory.translations.operator momentum state)
  positiveEnergy :
    theory.energyMomentum.projection forwardConeᶜ = 0
  uniqueVacuum (state : H.carrier) :
    (∀ x, theory.translations.operator x state = state) →
      ∃ scalar : ℂ, scalar • theory.fields.vacuum.1 = state

/-- W1: fields are tempered operator-valued distributions on a common dense
invariant domain, with the vacuum cyclic. -/
structure W1 (theory : WightmanTheory H Labels) : Prop where
  domain : theory.fields.DomainAxioms
  adjoint : theory.fields.AdjointAxiom theory.adjointLabel

/-- W2: Poincaré covariance of the fields and their common domain. -/
structure W2 (theory : WightmanTheory H Labels) : Prop where
  labelIdentity (label : Labels.carrier) :
    theory.poincare.onLabels 1 label = label
  labelComposition (g h : theory.poincare.Symmetry)
      (label : Labels.carrier) :
    theory.poincare.onLabels (g * h) label =
      theory.poincare.onLabels g (theory.poincare.onLabels h label)
  domainInvariant (g : theory.poincare.Symmetry) :
    Set.MapsTo (theory.poincare.onStates g)
      (theory.fields.domain : Set H.carrier) theory.fields.domain
  vacuumInvariant (g : theory.poincare.Symmetry) :
    theory.poincare.onStates g theory.fields.vacuum.1 =
      theory.fields.vacuum.1
  fieldCovariance (g : theory.poincare.Symmetry)
      (label : Labels.carrier) (test : TestFunction)
      (state : theory.fields.domain) :
    theory.poincare.onStates g (theory.fields.field label test state).1 =
      (theory.fields.field (theory.poincare.onLabels g label)
        (theory.poincare.onTests g test)
        ⟨theory.poincare.onStates g state.1,
          domainInvariant g state.2⟩).1

/-- W3: local commutativity at spacelike separation. -/
structure W3 (theory : WightmanTheory H Labels) : Prop where
  locality : theory.fields.LocalCommutativity

/-- The four Wightman axioms are separate fields so the Comparator checks
each one explicitly. -/
structure Axioms (theory : WightmanTheory H Labels) : Prop where
  w0 : W0 theory
  w1 : W1 theory
  w2 : W2 theory
  w3 : W3 theory

end WightmanTheory

end YangMills

end


/-! Four-dimensional periodic Wilson lattice and its ordered continuum limit. -/
noncomputable section
namespace YangMills
open MeasureTheory TopologicalSpace Filter Set
open scoped Topology BigOperators Distributions Matrix.Norms.Frobenius

abbrev Points (n : ℕ) := PiLp 2 (fun _ : Fin n => Spacetime)
abbrev Site (l : ℕ+) := Axis → ZMod l.val
abbrev Configuration (g : GaugeGroup) (l : ℕ+) := (Site l × Axis) → g.image
abbrev Directions := {p : Axis × Axis // p.1 < p.2}

namespace GaugeGroup
instance (g : GaugeGroup) : MeasurableSpace g.image := borel _
instance (g : GaugeGroup) : BorelSpace g.image := ⟨rfl⟩
end GaugeGroup

def plaquette {g : GaugeGroup} {l : ℕ+} (U : Configuration g l) (x : Site l)
    (i j : Axis) : g.image :=
  U (x,i) * (U (x + Pi.single i 1,j) *
    ((U (x + Pi.single j 1,i))⁻¹ * (U (x,j))⁻¹))

def wilsonEnergy {g : GaugeGroup} {l : ℕ+} (U : Configuration g l) : ℝ :=
  ∑ p : Site l × Directions,
    (1 - ((plaquette U p.1 p.2.val.1 p.2.val.2).val.val.trace).re / ((g.n+1 : ℕ) : ℝ))

def wilsonLaw (g : GaugeGroup) (l : ℕ+) (β : ℝ) (haar : Measure g.image) :
    Measure (Configuration g l) :=
  let prior : Measure (Configuration g l) := Measure.pi fun _ => haar
  let density := fun U : Configuration g l => Real.exp (-β * wilsonEnergy U)
  prior.withDensity fun U => ENNReal.ofReal (density U / ∫ V, density V ∂prior)

structure WilsonFamily (g : GaugeGroup) where
  period : ℕ → ℕ+
  denominator : ℕ → ℕ+
  periodStrict : StrictMono fun p => (period p).val
  denominatorStrict : StrictMono fun N => (denominator N).val
  beta : ℕ → ℕ → ℝ
  haar : Measure g.image
  probability : IsProbabilityMeasure haar
  invariantHaar : haar.IsHaarMeasure
  Token : Type
  insertion (N p : ℕ) : Token → Site (period p * denominator N) →
    Configuration g (period p * denominator N) → ℂ

namespace WilsonFamily
variable {g : GaugeGroup} (C : WilsonFamily g)
def mesh (N : ℕ) := ((C.denominator N).val : ℝ)⁻¹
def place (N p : ℕ) (y : Site (C.period p * C.denominator N)) : Spacetime :=
  WithLp.toLp 2 fun i => C.mesh N * (ZMod.valMinAbs (y i) : ℝ)

def finiteMoment (N p : ℕ) {n : ℕ} (labels : Fin n → C.Token)
    (x : Fin n → Site (C.period p * C.denominator N)) : ℂ :=
  ∫ U, ∏ i, C.insertion N p (labels i) (x i) U
    ∂wilsonLaw g (C.period p * C.denominator N) (C.beta N p) C.haar

def separated (n : ℕ) : Opens (Points n) :=
  ⟨{x | Function.Injective x.ofLp}, by
    classical
    have eqSet : {x : Points n | Function.Injective x.ofLp} =
        ⋂ (i : Fin n) (j : Fin n) (_ : i ≠ j), {x : Points n | x i ≠ x j} := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_iInter]
      exact ⟨fun h i j hij => fun he => hij (h he), fun h i j he => by_contra fun hij => h i j hij he⟩
    rw [eqSet]
    apply isOpen_iInter_of_finite; intro i
    apply isOpen_iInter_of_finite; intro j
    apply isOpen_iInter_of_finite; intro _
    exact isOpen_ne_fun (PiLp.continuous_apply _ _ i) (PiLp.continuous_apply _ _ j)⟩

abbrev SeparatedTest (n : ℕ) := _root_.TestFunction (separated n) ℂ ⊤

def suitable (p : ℕ) {n : ℕ} (t : SeparatedTest n) : Prop :=
  tsupport t ⊆ {x : Points n | ∀ i a, -((C.period p).val / (2:ℝ)) < x i a ∧
    x i a < (C.period p).val / (2:ℝ)}

def smear (N p : ℕ) {n : ℕ} (v : Fin n → C.Token) (t : SeparatedTest n) : ℂ :=
  (C.mesh N : ℂ) ^ (4*n) * ∑ x : Fin n → Site (C.period p * C.denominator N),
    t (WithLp.toLp 2 fun i => C.place N p (x i)) * C.finiteMoment N p v x

/-- Full mesh limit at each suitable fixed physical volume; then the
infinite-volume limit along the indicated strictly increasing sequence. -/
def Converges (volumeOrder : ℕ → ℕ)
    (unselected : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ) : Prop :=
  ∀ n (v : Fin n → C.Token) (t : SeparatedTest n),
    (∀ᶠ k : ℕ in atTop, C.suitable (volumeOrder k) t) ∧ ∃ row : ℕ → ℂ,
    (∀ p, C.suitable p t → Tendsto (fun N => C.smear N p v t) atTop (𝓝 (row p))) ∧
    Tendsto (fun k => row (volumeOrder k)) atTop (𝓝 (∫ x, t x * unselected v x))
end WilsonFamily
end YangMills
end


/-! The joint target. All correlation terms, including every spectator in the OPE,
are evaluations of one hierarchy. Finite lattice insertions precede every limit. -/
noncomputable section
namespace YangMills
open Function Filter Set MeasureTheory TopologicalSpace
open scoped Topology BigOperators InnerProductSpace Distributions Classical NNReal ContDiff

/-- A fixed finite lattice stencil for each insertion works at every spacing and volume. -/
structure WilsonRegularity {g : GaugeGroup} (C : WilsonFamily g) : Prop where
  running : ∃ slope : ℝ, 0 < slope ∧ ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ p, |C.beta N p / Real.log (C.mesh N)⁻¹ - slope| < ε
  continuous (N p v x) : Continuous (C.insertion N p v x)
  invariant (N p v x) (t : Site (C.period p * C.denominator N) → g.image) (U) :
    C.insertion N p v x (fun e => t e.1 * U e * (t (e.1 + Pi.single e.2 1))⁻¹) =
      C.insertion N p v x U
  localSupport (v : C.Token) : ∃ stencil : Finset (Axis → ℤ), ∀ N p (x : Site (C.period p * C.denominator N)),
    let sites := stencil.image fun z => (fun i => (z i : ZMod (C.period p * C.denominator N).val)) + x
    ∀ U V, (∀ e, e.1 ∈ sites → e.1 + Pi.single e.2 1 ∈ sites → U e = V e) →
      C.insertion N p v x U = C.insertion N p v x V

structure Hierarchy {g : GaugeGroup} (C : WilsonFamily g) where
  H : HilbertSpace
  labels : FieldLabels
  theory : WightmanTheory H labels
  Field : ℕ → Type
  [fieldAdd (d : ℕ) : NormedAddCommGroup (Field d)]
  [fieldSpace (d : ℕ) : NormedSpace ℂ (Field d)]
  [fieldFinite (d : ℕ) : FiniteDimensional ℂ (Field d)]
  toLabel (d : ℕ) : Field d →ₗ[ℂ] labels.carrier
  project : C.Token → (Σ d, Field d)
  Character : Type
  [characterMetric : MetricSpace Character]
  [characterSets : MeasurableSpace Character]
  [characterBorel : BorelSpace Character]
  [characterCompact : CompactSpace Character]
  phaseMeasure : Measure Character
  selected : Character
  correlation {n : ℕ} : Option Character → (Fin n → Σ d, Field d) → Points n → ℂ
  continuation {n : ℕ} : (Fin n → Σ d, Field d) → (Fin n → ℂ) → (Fin n → Space) → ℂ
  Channel : ℕ → Type
  [finiteChannels (d : ℕ) : Fintype (Channel d)]
  actor (d : ℕ) : Channel d → Field d
  coefficient {I : Type} [Fintype I] (a : I → Σ d, Field d) (j : ℕ) :
    Channel j → (I → Spacetime) → Spacetime → ℂ
  centeredTrace : Field 4
instance {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) (d : ℕ) :
    NormedAddCommGroup (T.Field d) := T.fieldAdd d
instance {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) (d : ℕ) :
    NormedSpace ℂ (T.Field d) := T.fieldSpace d
instance {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) (d : ℕ) :
    FiniteDimensional ℂ (T.Field d) := T.fieldFinite d
instance {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) (d : ℕ) :
    Fintype (T.Channel d) := T.finiteChannels d
instance {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) : MetricSpace T.Character :=
  T.characterMetric
instance {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) : MeasurableSpace T.Character :=
  T.characterSets
instance {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) : BorelSpace T.Character :=
  T.characterBorel
instance {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) : CompactSpace T.Character :=
  T.characterCompact

namespace Hierarchy
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
abbrev Tag := Σ d, T.Field d

/-- Enumerate the union of the insertion and spectator slots once, then read the hierarchy. -/
def grouped {I J : Type} [Fintype I] [Fintype J] (s : Option T.Character)
    (a : I → T.Tag) (x : I → Spacetime) (b : J → T.Tag) (y : J → Spacetime) : ℂ :=
  let slots := (Fintype.equivFin (I ⊕ J)).symm
  T.correlation s ((Sum.elim a b) ∘ slots) (WithLp.toLp 2 ((Sum.elim x y) ∘ slots))

def weight {I : Type} [Fintype I] (a : I → T.Tag) : ℝ := ∑ i, ((a i).1 : ℝ)

def Within {I : Type} (r M η : ℝ) (x : I → Spacetime) (o : Spacetime) : Prop :=
  (∀ i, ‖x i - o‖ ≤ M*r) ∧ (∀ i j, i ≠ j → η*r ≤ ‖x i - x j‖)
def Clear {J : Type} (o : Spacetime) (y : J → Spacetime) (c : ℝ) : Prop :=
  (∀ i, c ≤ ‖o - y i‖) ∧ (∀ i j, i ≠ j → c ≤ ‖y i - y j‖)

structure OperatorProductExpansion : Prop where
  coefficients {I : Type} [Fintype I] (a : I → T.Tag) (M η ε : ℝ) :
    0 ≤ M → 0 < η → 0 < ε → ∀ j (i : T.Channel j), ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ x o, Within r M η x o → ‖T.coefficient a j i x o‖ ≤ r ^ ((j:ℝ) - T.weight a - ε)
  remainder {I J : Type} [Fintype I] [Fintype J] (a : I → T.Tag) (b : J → T.Tag)
      (M η c ε : ℝ) : 0 ≤ M → 0 < η → 0 < c → 0 < ε → ∀ D : ℕ,
      ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x o y, Within r M η x o → Clear o y c → ∀ s,
      ‖T.grouped s a x b y -
        ∑ j : Fin (D+1), ∑ i : T.Channel j.val, T.coefficient a j.val i x o *
          T.grouped s (fun _ : Unit => ⟨j.val,T.actor j.val i⟩) (fun _ => o) b y‖
        ≤ r ^ ((D:ℝ) + 1 - T.weight a - ε)

/-- Four-dimensional Euclidean spacetime used by the OPE estimates. -/
abbrev OPEPoint := EuclideanSpace ℝ (Fin 4)

/-- Ordered configurations of `n` insertion points. -/
abbrev OPEPoints (n : ℕ) := PiLp 2 (fun _ : Fin n => OPEPoint)

/-- Complex time coordinates of an analytically continued correlation. -/
abbrev OPEComplexTimes (n : ℕ) := Fin n → ℂ

/-- Spatial coordinates of an analytically continued correlation. -/
abbrev OPESpacePoints (n : ℕ) := Fin n → OMA.S_wpc_yang_mills_existence_and_mass_gap.YangMills.Space

/-- The tube of complex times with strictly ordered imaginary parts. -/
def orderedTube (n : ℕ) : Set (OPEComplexTimes n) :=
  {z | StrictMono fun i ↦ (z i).im}

/-- Continue a real configuration into ordered imaginary-time directions. -/
def complexShift {n : ℕ} (r : ℝ) (height : Fin n → ℝ)
    (x : OPEPoints n) : OPEComplexTimes n :=
  fun i ↦ (OMA.S_wpc_yang_mills_existence_and_mass_gap.YangMills.time (x.ofLp i) : ℂ) +
    ((r * height i : ℝ) : ℂ) * Complex.I

/-- The purely imaginary times associated with a Euclidean configuration. -/
def imaginaryTimes {n : ℕ} (x : OPEPoints n) : OPEComplexTimes n :=
  fun i ↦ (OMA.S_wpc_yang_mills_existence_and_mass_gap.YangMills.time (x.ofLp i) : ℂ) * Complex.I

/-- Spatial coordinates of a Euclidean configuration. -/
def spatialPoints {n : ℕ} (x : OPEPoints n) : OPESpacePoints n :=
  fun i ↦ OMA.S_wpc_yang_mills_existence_and_mass_gap.YangMills.spatial (x.ofLp i)

/-- The product test used to smear an `n`-point correlation. -/
def tensorTest {n : ℕ} (tests : Fin n → OMA.S_wpc_yang_mills_existence_and_mass_gap.YangMills.TestFunction)
    (x : OPEPoints n) : ℂ :=
  ∏ i, tests i (x.ofLp i)

structure Reconstructed : Prop where
  wightman : T.theory.Axioms
  faithful : T.theory.fields.Faithful
  injective (d : ℕ) : Injective (T.toLabel d)
  acts : ∃ (a : T.Tag) (f : OMA.S_wpc_yang_mills_existence_and_mass_gap.YangMills.TestFunction), T.theory.fields.field (T.toLabel a.1 a.2) f ≠ 0
  covers : Surjective (fun a : T.Tag => T.toLabel a.1 a.2)
  represents : Surjective T.project
  normalized : IsProbabilityMeasure T.phaseMeasure
  fullSupport : T.phaseMeasure.IsOpenPosMeasure
  permutation (s : Option T.Character) {n : ℕ} (a : Fin n → T.Tag)
      (x : Points n) (hx : x ∈ WilsonFamily.separated n) (π : Equiv.Perm (Fin n)) :
    T.correlation s (a ∘ π) (WithLp.toLp 2 (x.ofLp ∘ π)) = T.correlation s a x
  smooth (s : Option T.Character) {n : ℕ} (a : Fin n → T.Tag) :
    ContDiffOn ℝ ∞ (T.correlation s a) (WilsonFamily.separated n)
  characterContinuity {n : ℕ} (a : Fin n → T.Tag) (x : Points n)
      (h : x ∈ WilsonFamily.separated n) : Continuous (fun i => T.correlation (some i) a x)
  mixture {n : ℕ} (a : Fin n → T.Tag) (x : Points n) (h : x ∈ WilsonFamily.separated n) :
    (∫ i, T.correlation (some i) a x ∂T.phaseMeasure) = T.correlation none a x
  analytic {n : ℕ} (v : Fin n → T.Tag) (space : OPESpacePoints n) :
    DifferentiableOn ℂ (fun z => T.continuation v z space) (orderedTube n)
  root {n : ℕ} (v : Fin n → T.Tag) (x : Points n) (h : StrictMono fun i => time (x i)) :
    T.continuation v (imaginaryTimes x) (spatialPoints x) = T.correlation (some T.selected) v x
  boundary {n : ℕ} (v : Fin n → T.Tag) (height : Fin n → ℝ) (h : StrictMono height)
      (tests : Fin n → OMA.S_wpc_yang_mills_existence_and_mass_gap.YangMills.TestFunction) :
    Tendsto (fun r => ∫ x : Points n, T.continuation v (complexShift r height x) (spatialPoints x) *
      tensorTest tests x) (𝓝[>] 0)
      (𝓝 (T.theory.fields.vacuumExpectation (fun i => T.toLabel (v i).1 (v i).2) tests))

/-- Two insertions on the time axis at -r/2 and r/2. -/
def timePair (r : ℝ) : Points 2 :=
  WithLp.toLp 2 fun i => WithLp.toLp 2 (Fin.snoc (fun _ : Fin 3 => (0:ℝ))
    (Fin.append (fun _ : Fin 1 => -(r/2)) (fun _ : Fin 1 => r/2) i))
def traceTwo (r : ℝ) := T.correlation (some T.selected) (fun _ : Fin 2 => ⟨4,T.centeredTrace⟩) (timePair r)

/-- Elementary mass-shell kernels, including finite differential orders. -/
structure Mode where
  mass : ℝ≥0
  spatialOrder : ℕ
  timeOrder : ℕ
  numerator : Space → ℝ
  continuous : Continuous numerator
  homogeneous (p : Space) (r : ℝ) : 0 < r → numerator (r • p) = r^spatialOrder * numerator p
def Mode.kernel (m : Mode) (r : ℝ) (p : Space) : ℝ :=
  let E := Real.sqrt ((m.mass:ℝ)^2 + ‖p‖^2)
  1 / (2*E) * E^m.timeOrder * m.numerator p * Real.exp (-r*E)
structure Track where
  n : ℕ
  modes : Fin n → Mode
def wickProfile (terms : List (ℂ × Track)) (r : ℝ) : ℂ :=
  (terms.map fun (c,t) => c * ((∏ i, ∫ p : Space, (t.modes i).kernel r p : ℝ) : ℂ)).sum

structure TraceTest : Prop where
  centered (f : OMA.S_wpc_yang_mills_existence_and_mass_gap.YangMills.TestFunction) :
    inner ℂ T.theory.fields.vacuum.1
      (T.theory.fields.field (T.toLabel 4 T.centeredTrace) f T.theory.fields.vacuum).1 = 0
  amplitudePositive : 0 < 3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi^4
  shortDistance : Tendsto (fun r : ℝ => (r^8 * (Real.log r⁻¹)^2) • T.traceTwo r)
    (𝓝[>] 0) (𝓝 ((3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi^4 : ℝ) : ℂ))
  excludes (terms : List (ℂ × Track)) : ¬ T.traceTwo =ᶠ[𝓝[>] 0] wickProfile terms

structure Properties (order : ℕ → ℕ) : Prop where
  wilson : C.Converges order (fun v => T.correlation none (T.project ∘ v))
  reconstruction : T.Reconstructed
  ope : T.OperatorProductExpansion
  nonfree : T.TraceTest
end Hierarchy


end YangMills
end


noncomputable section
namespace YangMills.Maxwell
open Function Set
open scoped BigOperators Topology InnerProductSpace Classical

abbrev Color (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Tensor (m j : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin j => Spacetime) (Color m)
abbrev TwoJet (m j : ℕ) := Axis → Axis → Tensor m j

def partialD {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : Axis) (f : Spacetime → V) (x : Spacetime) := fderiv ℝ f x (EuclideanSpace.single a 1)

def diagonal {m j : ℕ} (A : Tensor m j) (x : Spacetime) := A (fun _ => x)

/-- Ordinary curvature derivatives commute. The two form indices are antisymmetric,
and the Taylor two-form is closed and divergence-free. -/
def OnShell {m j : ℕ} (A : TwoJet m j) : Prop :=
  (∀ a b v (σ : Equiv.Perm (Fin j)), A a b (v ∘ σ) = A a b v) ∧
  (∀ a b, A a b = - A b a) ∧
  (∀ a b c x, partialD a (diagonal (A b c)) x + partialD b (diagonal (A c a)) x +
    partialD c (diagonal (A a b)) x = 0) ∧
  ∀ b x, ∑ a, partialD a (diagonal (A a b)) x = 0

/-- Coordinates on the specified shell, in a trace-normalized color frame. -/
structure Coordinates (g : GaugeGroup) where
  m : ℕ
  matrix : Color m →ₗ[ℝ] Matrix (Fin (g.n+1)) (Fin (g.n+1)) ℂ
  colors : LinearMap.range matrix = g.lieAlgebra
  traceForm (c e : Color m) : -(matrix c * matrix e).trace.re =
    ((g.n+1 : ℕ) : ℝ) * inner ℝ c e
  shell (j : ℕ) : Submodule ℝ (TwoJet m j)
  shell_iff (j) (A : TwoJet m j) : A ∈ shell j ↔ OnShell A
  rank : ℕ → ℕ
  basis (j : ℕ) : Module.Basis (Fin (rank j)) ℝ (shell j)
  rotate (u : g.image) (j : ℕ) : shell j →ₗ[ℝ] shell j
  adjoint (u : g.image) (j) (A : shell j) (a b v) :
    matrix ((rotate u j A).val a b v) = u.val.val * matrix (A.val a b v) * star u.val.val

namespace Coordinates
variable {g : GaugeGroup} (B : Coordinates g)
abbrev Key := (j : ℕ) × Fin (B.rank j)
abbrev Pol := MvPolynomial B.Key ℂ
abbrev Tower := (j : ℕ) → B.shell j

def eval (A : B.Tower) : B.Pol →ₐ[ℂ] ℂ := MvPolynomial.aeval
  fun i => ((B.basis i.1).repr (A i.1) i.2 : ℝ)

/-- The total monomial weight counts each order-j curvature factor with weight j+2. -/
def Admissible (d : ℕ) (p : B.Pol) : Prop :=
  p ∈ MvPolynomial.restrictSupport ℂ {s | Finsupp.weight (fun i : B.Key => i.1+2) s ≤ d} ∧
  ∀ u : g.image, ∀ A : B.Tower, B.eval (fun j => B.rotate u j (A j)) p = B.eval A p

end Coordinates
end YangMills.Maxwell
end


open YangMills MeasureTheory Filter Set
open scoped Topology BigOperators InnerProductSpace ContDiff

/-- Through each engineering dimension, the reconstructed local fields have
the filtered gauge-invariant curvature-polynomial content of the free
short-distance comparison. -/
def HasCurvatureFieldContent {g : GaugeGroup} {C : WilsonFamily g}
    (T : Hierarchy C) : Prop :=
  ∃ (B : Maxwell.Coordinates g) (sector : ℕ → Submodule ℂ B.Pol),
    (∀ d p, p ∈ sector d ↔ B.Admissible d p) ∧
    ∀ d, Nonempty (↥(sector d) ≃ₗ[ℂ] T.Field d)

/-- A window equals one near the first marked field and has compact smooth
support away from the spectator insertion points. -/
def TranslationWindow {n : ℕ} (x : Points (n + 1)) (χ : Spacetime → ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ χ =ᶠ[𝓝 (x 0)] (fun _ => 1) ∧
    ∀ i : Fin n, x i.succ ∉ tsupport χ

/-- Correlation with a component of the stress tensor at a new first point. -/
def stressCorrelation {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
    (phase : Option T.Character) (stress : Axis → Axis → T.Field 4)
    {n : ℕ} (fields : Fin (n + 1) → T.Tag) (x : Points (n + 1))
    (a b : Axis) (y : Spacetime) : ℂ :=
  T.correlation phase (Fin.cons ⟨4, stress a b⟩ fields)
    (WithLp.toLp 2 (Fin.cons y x.ofLp))

/-- The local stress tensor generates translations by its Ward identity, and
its centered trace is the same field used by the short-distance test. -/
def HasTranslationStressTensor {g : GaugeGroup} {C : WilsonFamily g}
    (T : Hierarchy C) : Prop :=
  ∃ (stress : Axis → Axis → T.Field 4) (unit : T.Field 4) (traceMean : ℂ),
    (∀ a b, stress a b = stress b a) ∧
    (∀ f : OMA.S_wpc_yang_mills_existence_and_mass_gap.YangMills.TestFunction,
      T.theory.fields.field (T.toLabel 4 unit) f =
        (∫ x : Spacetime, f x) • LinearMap.id) ∧
    (∑ a : Axis, stress a a) = T.centeredTrace + traceMean • unit ∧
    ∀ (phase : Option T.Character) (n : ℕ) (fields : Fin (n + 1) → T.Tag)
      (x : Points (n + 1)), x ∈ WilsonFamily.separated (n + 1) →
      ∀ (χ : Spacetime → ℝ), TranslationWindow x χ → ∀ b : Axis,
        (∀ a : Axis, Integrable (fun y : Spacetime =>
          ((Maxwell.partialD a χ y : ℝ) : ℂ) * stressCorrelation T phase stress fields x a b y)) ∧
        -(∑ a : Axis, ∫ y : Spacetime,
          ((Maxwell.partialD a χ y : ℝ) : ℂ) * stressCorrelation T phase stress fields x a b y) =
        fderiv ℝ (T.correlation phase fields) x (PiLp.single 2 0 (EuclideanSpace.single b 1))

/-- The spectral measure of the reconstructed time translations vanishes for
all energies strictly between zero and the gap, and has positive-energy spectrum
at a finite energy. -/
def PositiveFiniteMassGap {H : HilbertSpace} {L : FieldLabels}
    (T : WightmanTheory H L) : Prop :=
  ∃ gap cutoff : ℝ, 0 < gap ∧ 0 < cutoff ∧
    T.energyMomentum.projection {p | 0 < time p ∧ time p < gap} = 0 ∧
    T.energyMomentum.projection {p | 0 < time p ∧ time p < cutoff} ≠ 0

theorem main :
    ∀ g : GaugeGroup, g.IsSimple →
      ∃ C : WilsonFamily g, WilsonRegularity C ∧
      ∃ order : ℕ → ℕ, StrictMono order ∧
      ∃ T : Hierarchy C, T.Properties order ∧ HasCurvatureFieldContent T ∧
        HasTranslationStressTensor T ∧ PositiveFiniteMassGap T.theory := by
  sorry

end OMA.S_wpc_yang_mills_existence_and_mass_gap

/-
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
