import Mathlib

/-!
# The Almost Stacked Hypothesis: the tree stacking conjecture

Source: https://arxiv.org/abs/2610.09650 (T. Csernák, L. Soukup, v1, 7 Oct 2026), Conjecture 5.6
Credit: @landvaluetaxfan (agent: claude-code, model claude-opus-5-5)

Conjecture 5.6: if `T` is a finite connected tree, then `stack(T) = estim(T)`.

The paper proves `stack(T) ≥ estim(T)` unconditionally (Theorem 5.2) and the reverse inequality
under the Almost Stacked Hypothesis (Corollary 5.5). This file states only Conjecture 5.6, with no
hypothesis; ASH itself is not part of the statement.

## Definitions (Section 2 and Definition 5.1 of the source)

* A configuration on `G` is a function `c : V → ℕ`; its size is `‖c‖ = ∑ v, c v`.
* A pebbling step `u ⇒ v` along an edge `uv` applies when `c u ≥ 2`; it removes two pebbles from
  `u` and adds one to `v`. `Reach G c d` is reachability by a finite (possibly empty) sequence of
  steps.
* `c` is stacked if its support has exactly one vertex, and stackable if some stacked
  configuration is reachable from it.
* `stack G` is the least integer `t ≥ 2` such that every configuration of size `t` is stackable
  (defined in the source for connected graphs).
* For a tree `T` and a vertex `r`: `leaf_T(r)` is the number of leaves (degree-one vertices) other
  than `r`, and `ρ_T(r) = ∑ deg(v) · 2^dist(r, v)` over the vertices `v` with `v = r` or
  `deg v > 1`.
* `estim(T) = max {2, 1 + max_r (ρ_T(r) + leaf_T(r))}`.

## Conventions

* A finite tree is a finite type with a simple graph satisfying Mathlib's `SimpleGraph.IsTree`
  (connected, hence nonempty, and acyclic). This is the source's finite connected tree.
* The one-vertex tree is included, as in the source: there `stack = 2 = estim` (proof of
  Theorem 5.2), and the `max {2, …}` term handles it.
* `stack` uses `sInf` on `ℕ`; the set is nonempty for every finite connected graph, so this is the
  source's minimum.
-/

namespace OMA.S_arxiv_2610_09650

open scoped Classical

/-- The size `‖c‖` of a configuration `c : V → ℕ`. -/
def size {V : Type} [Fintype V] (c : V → ℕ) : ℕ :=
  ∑ v, c v

/-- One pebbling step `u ⇒ v` along an edge of `G`: two pebbles leave `u`, one arrives at `v`. -/
def PebblingStep {V : Type} (G : SimpleGraph V) (c d : V → ℕ) : Prop :=
  ∃ u v, G.Adj u v ∧ 2 ≤ c u ∧
    d = Function.update (Function.update c u (c u - 2)) v (c v + 1)

/-- `d` is reachable from `c` by finitely many pebbling steps (`c ↦ d` in the source). -/
def Reach {V : Type} (G : SimpleGraph V) (c d : V → ℕ) : Prop :=
  Relation.ReflTransGen (PebblingStep G) c d

/-- A configuration is stacked if its support has exactly one vertex. -/
def IsStacked {V : Type} (c : V → ℕ) : Prop :=
  ∃ r, 0 < c r ∧ ∀ v, v ≠ r → c v = 0

/-- A configuration is stackable if some stacked configuration is reachable from it. -/
def Stackable {V : Type} (G : SimpleGraph V) (c : V → ℕ) : Prop :=
  ∃ d, Reach G c d ∧ IsStacked d

/-- The stacking number: the least `t ≥ 2` such that every configuration of size `t` is
stackable. -/
noncomputable def stack {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {t : ℕ | 2 ≤ t ∧ ∀ c : V → ℕ, size c = t → Stackable G c}

/-- `leaf_T(r)`: the number of leaves (degree-one vertices) of `T` other than `r`. -/
noncomputable def leafCount {V : Type} [Fintype V] (T : SimpleGraph V) (r : V) : ℕ :=
  (Finset.univ.filter fun v => v ≠ r ∧ T.degree v = 1).card

/-- `ρ_T(r)`: the sum of `deg(v) · 2 ^ dist(r, v)` over the vertices `v` with `v = r` or
`deg(v) > 1`. -/
noncomputable def rho {V : Type} [Fintype V] (T : SimpleGraph V) (r : V) : ℕ :=
  ∑ v ∈ Finset.univ.filter (fun v => v = r ∨ 1 < T.degree v), T.degree v * 2 ^ T.dist r v

/-- `estim(T) = max {2, 1 + max_r (ρ_T(r) + leaf_T(r))}`. -/
noncomputable def estim {V : Type} [Fintype V] (T : SimpleGraph V) : ℕ :=
  max 2 (1 + Finset.univ.sup fun r => rho T r + leafCount T r)

/-- Conjecture 5.6 of Csernák–Soukup: every finite tree `T` satisfies `stack(T) = estim(T)`. -/
theorem main :
    ∀ (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree → stack T = estim T := by
  sorry

end OMA.S_arxiv_2610_09650
