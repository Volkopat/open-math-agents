import Mathlib

/-!
# Circular-arc graphs are chromatic-choosable

Source: https://mathoverflow.net/questions/456166, asked by MathOverflow user CTVK (2023):
"Is the choosability/list chromatic number of a circular arc graph equal to its chromatic
number?" Prowse and Woodall (Graphs Combin. 2003) proved `χ_ℓ(C_n^k) = χ(C_n^k)` for powers of
cycles and conjectured that the equality holds for all circular-arc graphs (the Prowse–Woodall
conjecture). It was proved by R. Tao, *List colouring of circular-arc graphs*,
arXiv:2611.20947v1 (16 Nov 2026), Theorem 1.1: `χ_L(G) = χ(G)` for every circular-arc graph `G`.
The mathematics is Tao's; this file only states it.

Translation choices.
* The circle is `ℝ / ℤ`, represented by real numbers read modulo `1` through `Int.fract`.
* A closed arc is given by a start point `a : ℝ` and a length `ℓ ≥ 0`; the point `x` lies on it
  when `Int.fract (x - a) ≤ ℓ`, i.e. when `x` is reached from `a` by moving forward at most `ℓ`
  around the circle. A length `ℓ ≥ 1` gives the whole circle and `ℓ = 0` a single point, so every
  arc is nonempty and closed, and every nonempty closed arc of `ℝ / ℤ` arises this way.
* A graph `G` on a vertex type `V` is a circular-arc graph when there are arcs `X_v` (`v : V`)
  such that distinct `u, v` are adjacent exactly when `X_u ∩ X_v ≠ ∅` (arcs may repeat).
* The graph is finite (`Finite V`), as in the paper.
* `IsKChoosable G k`: every assignment of lists `L v ⊆ ℕ` with `|L v| = k` admits a proper
  colouring `C : G.Coloring ℕ` with `C v ∈ L v` (Erdős–Rubin–Taylor; same definition as
  `SimpleGraph.IsKChoosable` in formal-conjectures).
* `main`: a `k`-colourable circular-arc graph is `k`-choosable. Since `k`-choosable graphs are
  `k`-colourable, this is `χ_L(G) = χ(G)`.
-/

namespace OMA.S_mo_456166

/-- `x` lies on the closed arc of `ℝ / ℤ` that starts at `a` and has length `ℓ`. -/
def OnArc (a ℓ x : ℝ) : Prop := Int.fract (x - a) ≤ ℓ

/-- `G` is the intersection graph of a family of nonempty closed arcs of the circle `ℝ / ℤ`. -/
def IsCircularArcGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a ℓ : V → ℝ, (∀ v, 0 ≤ ℓ v) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ ∃ x, OnArc (a u) (ℓ u) x ∧ OnArc (a v) (ℓ v) x)

/-- `G` is `k`-choosable: every assignment of `k`-element lists admits a proper list colouring. -/
def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) → ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v

theorem main : ∀ {V : Type*} [Finite V] (G : SimpleGraph V), IsCircularArcGraph G →
    ∀ k : ℕ, G.Colorable k → IsKChoosable G k := by
  sorry

end OMA.S_mo_456166
