import Mathlib

/-!
# Grünbaum–Nash-Williams conjecture

Source: https://en.wikipedia.org/wiki/Grünbaum–Nash-Williams_conjecture
Credit: @Folqr

**The conjecture (Wikipedia):** "every 4-vertex-connected toroidal graph has a
Hamiltonian cycle." It generalizes Tutte's theorem that every 4-vertex-connected
planar graph has a Hamiltonian cycle; Thomas and Yu proved the analogous statement
for the projective plane, and the 5-connected toroidal case.

## Formalization conventions

* "4-vertex-connected" is spelled out: the graph has at least five vertices and
  remains connected after the deletion of any set of at most three vertices
  (vertex-connectivity at least 4).
* "Toroidal" means embeddable in the torus, i.e. of orientable genus at most 1.
  By the Edmonds rotation-system correspondence, a connected graph has orientable
  genus ≤ 1 if and only if it admits a rotation system (a cyclic order of the darts
  at every vertex) whose associated face-tracing permutation has at least `E - V`
  orbits, i.e. Euler characteristic `V - E + F ≥ 0`. We use this combinatorial
  encoding: a `RotationSystem` is a permutation `σ` of the darts that preserves the
  tail and is a single cycle on the darts at each vertex, and the faces are the
  orbits of the face permutation `σ ∘ α`, where `α` is dart reversal.
  (Simple graphs have no loops and no parallel edges, which is what the dart
  formalization assumes.)
* "Has a Hamiltonian cycle" is `SimpleGraph.IsHamiltonian`, Mathlib's standard
  predicate (its `Fintype.card ≠ 1` side condition is vacuous here, since a
  4-vertex-connected graph has at least five vertices).
-/

namespace OMA.S_wp_grunbaum_nash_williams_conjecture

open SimpleGraph

variable {V : Type} (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The set of orbits of the powers of a permutation of the darts.  For a
bijection of a finite type these orbits partition the dart set; they are the
faces of the combinatorial map given by the rotation system. -/
def faceOrbits (φ : G.Dart ≃ G.Dart) : Set (Set G.Dart) :=
  Set.range fun d : G.Dart => Set.range fun k : ℕ => (φ ^ k) d

/-- The number of faces of the combinatorial map determined by a permutation of
the darts: the number of orbits of its powers. -/
noncomputable def faceCount (φ : G.Dart ≃ G.Dart) : ℕ :=
  Nat.card (faceOrbits G φ)

/-- A rotation system for `G`: a permutation `σ` of the darts that fixes the tail
of each dart (it rotates the darts ending at the dart's tail vertex) and whose
restriction to the darts at each vertex is a single cycle (a cyclic order of the
darts ending at that vertex). -/
def IsRotationSystem (σ : G.Dart ≃ G.Dart) : Prop :=
  (∀ d : G.Dart, (σ d).toProd.1 = d.toProd.1) ∧
    ∀ d d' : G.Dart, d'.toProd.1 = d.toProd.1 → ∃ k : ℕ, (σ ^ k) d = d'

/-- The face permutation `φ = σ ∘ α` of a rotation system `σ`, where `α` is dart
reversal (`Dart.symm`).  Its orbits are the faces of the combinatorial map. -/
def facePerm (σ : G.Dart ≃ G.Dart) : G.Dart ≃ G.Dart where
  toFun d := σ d.symm
  invFun d := (σ.symm d).symm
  left_inv d := by simp [Dart.symm_symm]
  right_inv d := by simp [Dart.symm_symm]

/-- `G` is toroidal: it has orientable genus at most 1, encoded as the existence
of a rotation system whose face count makes the Euler characteristic
`V - E + F` nonnegative (genus `(2 - (V - E + F)) / 2 ≤ 1`). -/
def Toroidal : Prop :=
  ∃ σ : G.Dart ≃ G.Dart, IsRotationSystem G σ ∧
    (Fintype.card V : ℤ) - G.edgeFinset.card + (faceCount G (facePerm G σ) : ℤ) ≥ 0

/-- `G` is 4-vertex-connected: at least five vertices, and connected after the
deletion of any set of at most three vertices. -/
def FourConnected : Prop :=
  5 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card ≤ 3 → (G.induce ((S : Set V)ᶜ)).Connected

/-- **Grünbaum–Nash-Williams conjecture** (early 1970s, Branko Grünbaum and
Crispin Nash-Williams): every 4-vertex-connected toroidal graph has a
Hamiltonian cycle. -/
theorem main : ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj], FourConnected G → Toroidal G → G.IsHamiltonian := by
  sorry

end OMA.S_wp_grunbaum_nash_williams_conjecture
