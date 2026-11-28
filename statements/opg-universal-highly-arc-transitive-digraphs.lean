import Mathlib

/-!
# Universal highly arc transitive digraphs

Source: https://www.openproblemgarden.org/op/universal_highly_arc_transitive_digraphs
Credit: @lzvxck

The source: an alternating walk in a digraph is a walk `v_0, e_1, v_1, ..., v_m` so that the
vertex `v_i` is either the head of both `e_i` and `e_{i+1}` or the tail of both, for every
`1 ≤ i ≤ m - 1`. A digraph is universal if for every pair of edges `e, f` there is an
alternating walk containing both. For `s ≥ 0`, an `s`-arc is a sequence `(x_0, ..., x_s)` of
vertices with `(x_i, x_{i+1})` an edge for every `0 ≤ i ≤ s - 1` and `x_{i-1} ≠ x_{i+1}` for
every `1 ≤ i ≤ s - 1`. `D` is `s`-arc transitive if its automorphism group acts transitively
on the set of `s`-arcs, and highly arc transitive if it is `s`-arc transitive for every `s`.
Question: does there exist a locally finite highly arc transitive digraph which is universal?

The existence (affirmative) form is stated. Conventions:
* A digraph is a relation `Adj` on a vertex type `V` (Mathlib's `Digraph`); its edges are the
  pairs `(a, b)` with `Adj a b`. Digraphs here have no loops and at least one edge (without
  these, a single vertex with a loop, or with no edge, would be a trivial example).
* Locally finite: every vertex has finitely many out-neighbours and in-neighbours.
* Automorphisms are permutations `σ` of `V` with `Adj (σ a) (σ b) ↔ Adj a b`.
* In an alternating walk the edges alternate between being traversed forwards and backwards
  (a vertex that is the head of both `e_i` and `e_{i+1}` is entered forwards and left
  backwards, and similarly for tails). So it is given by its vertices `v : Fin (m+1) → V` and
  by whether the first edge is traversed forwards; edge `i` is then the pair
  `(v i, v (i+1))` or `(v (i+1), v i)`.
-/

namespace OMA.S_opg_universal_highly_arc_transitive_digraphs

/-- `x` is an `s`-arc of `D`. -/
def IsSArc {V : Type*} (D : Digraph V) {s : ℕ} (x : Fin (s + 1) → V) : Prop :=
  (∀ i : Fin s, D.Adj (x i.castSucc) (x i.succ)) ∧
    ∀ i : ℕ, ∀ h : i + 2 < s + 1, x ⟨i, by omega⟩ ≠ x ⟨i + 2, h⟩

/-- `D` is highly arc transitive: for every `s`, automorphisms act transitively on `s`-arcs. -/
def IsHighlyArcTransitive {V : Type*} (D : Digraph V) : Prop :=
  ∀ (s : ℕ) (x y : Fin (s + 1) → V), IsSArc D x → IsSArc D y →
    ∃ σ : V ≃ V, (∀ a b, D.Adj (σ a) (σ b) ↔ D.Adj a b) ∧ ∀ i, σ (x i) = y i

/-- Edge `i` of the alternating walk with vertices `v`, whose first edge is traversed forwards
iff `fwd` holds: edges at even positions go the same way as the first one. -/
def altEdge {V : Type*} {m : ℕ} (v : Fin (m + 1) → V) (fwd : Bool) (i : Fin m) : V × V :=
  if (Even (i : ℕ) ↔ fwd = true) then (v i.castSucc, v i.succ) else (v i.succ, v i.castSucc)

/-- `D` is universal: any two edges lie on a common alternating walk. -/
def IsUniversal {V : Type*} (D : Digraph V) : Prop :=
  ∀ a b c d : V, D.Adj a b → D.Adj c d →
    ∃ (m : ℕ) (v : Fin (m + 1) → V) (fwd : Bool),
      (∀ i, D.Adj (altEdge v fwd i).1 (altEdge v fwd i).2) ∧
      (∃ i, altEdge v fwd i = (a, b)) ∧ ∃ j, altEdge v fwd j = (c, d)

/-- **Universal highly arc transitive digraphs (Cameron, Praeger, Wormald).** There is a
loopless, locally finite, highly arc transitive digraph with at least one edge which is
universal. -/
theorem main : ∃ (V : Type) (D : Digraph V),
    (∀ v, ¬ D.Adj v v) ∧ (∃ a b, D.Adj a b) ∧
    (∀ v, {w | D.Adj v w}.Finite ∧ {w | D.Adj w v}.Finite) ∧
    IsHighlyArcTransitive D ∧ IsUniversal D := by
  sorry

end OMA.S_opg_universal_highly_arc_transitive_digraphs
