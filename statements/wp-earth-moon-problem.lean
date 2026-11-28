import Mathlib

/-!
# Earth–Moon problem

Source: https://en.wikipedia.org/wiki/Earth–Moon_problem
Credit: @eltociear

Ringel's Earth–Moon problem (1959): what is the maximum chromatic number of biplanar graphs?
It is known to be at least `9` (Sulanke, 1974: `K₆` joined with `C₅`) and at most `12`
(a biplanar graph on `n` vertices has at most `6n - 12` edges, so it is `11`-degenerate).
Ringel's original guess of `8` was refuted by Sulanke's example. The source records Ellen
Gethner's 2018 conjecture that the correct number is `11`; following the rule "state the
conjectured answer when the source gives one", `main` states that conjecture: the maximum of
the chromatic numbers of biplanar graphs exists and equals `11`.

Conventions (standard, as in the source):
- Graphs are finite simple graphs, given as a `SimpleGraph` on a finite vertex type `V`. The
  source's maps have finitely many countries, so the graphs are finite.
- A graph is planar if it has a plane drawing: distinct points of `ℝ²` for the vertices and,
  for every edge, an arc (a continuous injective image of `[0, 1]`) joining its endpoints,
  whose interior meets no vertex and no other edge's interior. This is the definition used in
  `statements/wp-apex-graph.lean`, copied verbatim.
- A graph is biplanar (has thickness at most two) if its edges can be split into two sets that
  each form a planar graph. It is stated as `G = G₁ ⊔ G₂` with `G₁`, `G₂` planar. This is the
  same as an edge partition: given a cover, delete the edges of `G₁` from `G₂`, which keeps it
  planar, since a subgraph of a planar graph is planar.
- Chromatic numbers are Mathlib's `SimpleGraph.chromaticNumber`, valued in `ℕ∞`. "The maximum
  is `11`" is stated as `IsGreatest`: some biplanar graph has chromatic number `11`, and every
  biplanar graph has chromatic number at most `11`.
-/

namespace OMA.S_wp_earth_moon_problem

open SimpleGraph

/-- `G` has a plane drawing: vertices at distinct points, edges as arcs joining their endpoints,
with arc interiors avoiding all vertices and the interiors of all other arcs. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (pos : V → ℝ × ℝ) (arc : G.edgeSet → C(unitInterval, ℝ × ℝ)),
    Function.Injective pos ∧
    (∀ e, Function.Injective (arc e)) ∧
    (∀ e, Sym2.map pos e.1 = s(arc e 0, arc e 1)) ∧
    (∀ e (t : unitInterval), (t : ℝ) ∈ Set.Ioo 0 1 → ∀ v, arc e t ≠ pos v) ∧
    (∀ e f, e ≠ f → ∀ s t : unitInterval, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      arc e s ≠ arc f t)

/-- `G` is biplanar (thickness at most two): it is the union of two planar graphs on the same
vertex set. -/
def IsBiplanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ G₁ G₂ : SimpleGraph V, IsPlanar G₁ ∧ IsPlanar G₂ ∧ G = G₁ ⊔ G₂

/-- Gethner's conjecture: the maximum chromatic number of finite biplanar graphs is `11`. -/
theorem main :
    IsGreatest
      {k : ℕ∞ | ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        IsBiplanar G ∧ G.chromaticNumber = k}
      11 := by
  sorry

end OMA.S_wp_earth_moon_problem
