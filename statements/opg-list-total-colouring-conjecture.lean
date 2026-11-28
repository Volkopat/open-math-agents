import Mathlib

/-!
# List Total Colouring Conjecture

Source: http://www.openproblemgarden.org/op/list_total_colouring_conjecture
Credit: @shc261392

Conjecture (Borodin, Kostochka and Woodall). If `T` is the total graph of a multigraph, then
the list chromatic number of `T` equals its chromatic number.

Reading used here:
* A finite multigraph is given by finite types `V` (vertices) and `E` (edges) and a map
  `ends : E → Sym2 V`, with no loops (`¬ (ends e).IsDiag`); parallel edges are allowed.
* Its total graph lives on `V ⊕ E`: two vertices are adjacent when some edge joins them, two
  distinct edges are adjacent when they share an endpoint, and a vertex is adjacent to an
  edge when it is incident with it.
* Since the list chromatic number is always at least the chromatic number, equality says:
  whenever the total graph has a proper colouring with `k` colours, every assignment of lists
  of size at least `k` (lists drawn from `ℕ`, which loses nothing for finite graphs) admits a
  proper colouring choosing each colour from its own list.
-/

namespace OMA.S_opg_list_total_colouring_conjecture

/-- The total graph of the multigraph `ends`. -/
def totalGraph {V E : Type*} (ends : E → Sym2 V) : SimpleGraph (V ⊕ E) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | Sum.inl u, Sum.inl v => ∃ e, ends e = s(u, v)
    | Sum.inr e, Sum.inr f => e ≠ f ∧ ∃ v, v ∈ ends e ∧ v ∈ ends f
    | Sum.inl v, Sum.inr e => v ∈ ends e
    | Sum.inr e, Sum.inl v => v ∈ ends e

/-- `G` is `k`-choosable: every list assignment with lists of size at least `k` admits a
proper colouring from the lists. -/
def Choosable {W : Type*} (G : SimpleGraph W) (k : ℕ) : Prop :=
  ∀ L : W → Finset ℕ, (∀ w, k ≤ (L w).card) →
    ∃ c : W → ℕ, (∀ w, c w ∈ L w) ∧ ∀ x y, G.Adj x y → c x ≠ c y

theorem main :
    ∀ (V E : Type) [Fintype V] [Fintype E] (ends : E → Sym2 V),
      (∀ e, ¬ (ends e).IsDiag) →
      ∀ k : ℕ, (totalGraph ends).Colorable k → Choosable (totalGraph ends) k := by
  sorry

end OMA.S_opg_list_total_colouring_conjecture
