import Mathlib

/-!
# Crossing sequences

Source https://www.openproblemgarden.org/op/crossing_sequences

Every finite strictly decreasing sequence of nonnegative integers ending
in zero is realizable as an orientable crossing sequence and as a
nonorientable crossing sequence, with independent graphs for the two cases.
-/

namespace OMA.S_opg_crossing_sequences

open AlgebraicTopology

abbrev Plane := EuclideanSpace ℝ (Fin 2)

structure ClosedSurface where
  space : TopCat
  hausdorff : T2Space space
  secondCountable : SecondCountableTopology space
  compact : CompactSpace space
  connected : ConnectedSpace space
  charts : ChartedSpace Plane space

inductive SurfaceKind
  | orientable
  | nonorientable

noncomputable def firstBetti (K : Type) [Field K] (S : TopCat) : ℕ :=
  Module.finrank K
    (((singularHomologyFunctor (ModuleCat K) 1).obj (ModuleCat.of K K)).obj S)

/-- The rational and mod-two first Betti numbers distinguish closed
surfaces by orientability and genus. Genus zero uses the sphere for
both sequences. -/
def HasGenus (S : ClosedSurface) (kind : SurfaceKind) (g : ℕ) : Prop :=
  let rational := firstBetti ℚ S.space
  let modTwo := firstBetti (ZMod 2) S.space
  match kind, g with
  | .orientable, g => rational = 2 * g ∧ modTwo = 2 * g
  | .nonorientable, 0 => rational = 0 ∧ modTwo = 0
  | .nonorientable, g + 1 => rational = g ∧ modTwo = g + 1

/-- Increasing endpoints give one index for each simple undirected edge. -/
abbrev Edge {n : ℕ} (G : SimpleGraph (Fin n)) :=
  { p : Fin n × Fin n // p.1 < p.2 ∧ G.Adj p.1 p.2 }

structure Drawing {n : ℕ} (G : SimpleGraph (Fin n)) (S : TopCat) where
  vertex : Fin n ↪ S
  arc : ∀ e : Edge G, Path (vertex e.1.1) (vertex e.1.2)
  arc_injective : ∀ e, Function.Injective (arc e)
  vertex_on_arc : ∀ v e t, vertex v = arc e t → v = e.1.1 ∨ v = e.1.2

def Drawing.edgeImage {n : ℕ} {G : SimpleGraph (Fin n)} {S : TopCat}
    (D : Drawing G S) (e : Edge G) : Set S :=
  Set.range (D.arc e)

def Drawing.crossings {n : ℕ} {G : SimpleGraph (Fin n)} {S : TopCat}
    (D : Drawing G S) : Set S :=
  {x | x ∉ Set.range D.vertex ∧ ∃ e f : Edge G, e ≠ f ∧
    x ∈ D.edgeImage e ∧ x ∈ D.edgeImage f}

/-- At each intersection away from vertices there are exactly two
edges, and a local chart sends them to the two coordinate axes. -/
def Drawing.HasOrdinaryCrossings {n : ℕ} {G : SimpleGraph (Fin n)} {S : TopCat}
    (D : Drawing G S) : Prop :=
  ∀ (x : S) (e f : Edge G), x ∉ Set.range D.vertex → e ≠ f →
    x ∈ D.edgeImage e → x ∈ D.edgeImage f →
    (∀ g : Edge G, x ∈ D.edgeImage g → g = e ∨ g = f) ∧
    ∃ h : OpenPartialHomeomorph S Plane, x ∈ h.source ∧ h x = 0 ∧
      h '' (D.edgeImage e ∩ h.source) = {y ∈ h.target | y 0 = 0} ∧
      h '' (D.edgeImage f ∩ h.source) = {y ∈ h.target | y 1 = 0}

def HasDrawingWithCrossings {n : ℕ} (G : SimpleGraph (Fin n))
    (kind : SurfaceKind) (g a : ℕ) : Prop :=
  ∃ (S : ClosedSurface) (D : Drawing G S.space), HasGenus S kind g ∧
    D.HasOrdinaryCrossings ∧ D.crossings.Finite ∧ D.crossings.ncard = a

def HasCrossingNumber {n : ℕ} (G : SimpleGraph (Fin n))
    (kind : SurfaceKind) (g a : ℕ) : Prop :=
  HasDrawingWithCrossings G kind g a ∧
    ∀ b : ℕ, HasDrawingWithCrossings G kind g b → a ≤ b

theorem main :
    ∀ (n : ℕ) (a : Fin (n + 1) → ℕ), StrictAnti a → a (Fin.last n) = 0 →
      ∀ kind : SurfaceKind, ∃ (v : ℕ) (G : SimpleGraph (Fin v)),
        ∀ i : Fin (n + 1), HasCrossingNumber G kind i.val (a i) := by
  sorry

end OMA.S_opg_crossing_sequences
