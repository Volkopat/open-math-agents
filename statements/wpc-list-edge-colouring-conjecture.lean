import Mathlib

/-!
# List edge-colouring conjecture

Source: https://en.wikipedia.org/wiki/List_edge-coloring
Credit: @mgv27

For every (multi)graph G, the list chromatic index equals the chromatic index: if every edge is
given a list of χ′(G) colours, the edges can be properly coloured choosing each colour from the
edge's list. Proved for bipartite multigraphs by Galvin (1995) and asymptotically by Kahn.

Formalization notes:
* A finite loopless multigraph is a finite edge type `E` with `ends : E → Sym2 V`, no edge
  being a loop; parallel edges are allowed. The vertex type `V` is arbitrary.
* Two distinct edges conflict if they share an endpoint. Colours are natural numbers.
* `χ'(G)` is the least `k` admitting a proper colouring with colours `< k`.
* `main` states the list form: any lists of size `χ'(G)` admit a proper list colouring
  (the inequality `χ' ≤ ch'` is trivial).
-/

namespace OMA.S_wpc_list_edge_colouring_conjecture

/-- Distinct edges `e`, `f` share an endpoint. -/
def Adj {V E : Type} (ends : E → Sym2 V) (e f : E) : Prop :=
  e ≠ f ∧ ∃ v, v ∈ ends e ∧ v ∈ ends f

/-- `c` is a proper edge colouring: conflicting edges get different colours. -/
def IsProper {V E : Type} (ends : E → Sym2 V) (c : E → ℕ) : Prop :=
  ∀ e f, Adj ends e f → c e ≠ c f

/-- The chromatic index: least `k` with a proper colouring using colours `< k`. -/
noncomputable def chromaticIndex {V E : Type} (ends : E → Sym2 V) : ℕ :=
  sInf {k : ℕ | ∃ c : E → ℕ, IsProper ends c ∧ ∀ e, c e < k}

/-- List edge-colouring conjecture. -/
theorem main : ∀ (V E : Type) [Fintype E] (ends : E → Sym2 V), (∀ e, ¬ (ends e).IsDiag) →
    ∀ L : E → Finset ℕ, (∀ e, (L e).card = chromaticIndex ends) →
    ∃ c : E → ℕ, IsProper ends c ∧ ∀ e, c e ∈ L e := by
  sorry

end OMA.S_wpc_list_edge_colouring_conjecture
