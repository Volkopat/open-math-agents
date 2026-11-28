import Mathlib

/-!
# Almost all non-Hamiltonian 3-regular graphs are 1-connected

Source: https://www.openproblemgarden.org/op/almost_all_non_hamiltonian_3_regular_graphs_are_1_connected
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Filar, Haythorpe, Nguyen): let `NH(n)` be the number of non-Hamiltonian 3-regular
graphs on `2n` vertices and `NHB(n)` the number of non-Hamiltonian 3-regular 1-connected graphs
on `2n` vertices. Then `NHB(n) / NH(n) → 1` as `n → ∞`.

## Encoding

* Graphs are counted up to isomorphism: `NH n` is the number of isomorphism classes of simple
  graphs on `Fin (2 * n)` with the property.
* Following the source paper ("A conjecture on the prevalence of cubic bridge graphs"), the
  graphs counted are connected; "1-connected" means connectivity exactly one, i.e. connected
  and having a cut vertex (for cubic graphs, equivalently a bridge).
* Hamiltonicity: Mathlib's `SimpleGraph.IsHamiltonian`.
* The ratio is taken in `ℝ` (for small `n` where `NH n = 0` Lean's `x / 0 = 0` applies, which
  does not affect the limit).
-/

namespace OMA.S_opg_almost_all_non_hamiltonian_3_regular_graphs_are_1_connected

open SimpleGraph Filter Topology

/-- Connected, cubic and non-Hamiltonian. -/
def IsNH {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  G.Connected ∧ (∀ v, (G.neighborSet v).ncard = 3) ∧ ¬ G.IsHamiltonian

/-- Additionally 1-connected: some vertex is a cut vertex. -/
def IsNHB {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  IsNH G ∧ ∃ v : V, ¬ (G.induce ({v}ᶜ : Set V)).Connected

/-- Isomorphism of graphs on `Fin m`, as a setoid on graphs with a property `p`. -/
def isoSetoid (m : ℕ) (p : SimpleGraph (Fin m) → Prop) : Setoid {G // p G} where
  r G H := Nonempty (G.1 ≃g H.1)
  iseqv := ⟨fun G => ⟨Iso.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨f.comp e⟩⟩

/-- Number of isomorphism classes of graphs on `m` vertices with property `p`. -/
noncomputable def countIso (m : ℕ) (p : SimpleGraph (Fin m) → Prop) : ℕ :=
  Nat.card (Quotient (isoSetoid m p))

/-- `NH n`: non-Hamiltonian cubic graphs on `2n` vertices, up to isomorphism. -/
noncomputable def NH (n : ℕ) : ℕ := countIso (2 * n) IsNH

/-- `NHB n`: the 1-connected ones among them. -/
noncomputable def NHB (n : ℕ) : ℕ := countIso (2 * n) IsNHB

theorem main :
    Tendsto (fun n : ℕ => (NHB n : ℝ) / NH n) atTop (𝓝 1) := by
  sorry

end OMA.S_opg_almost_all_non_hamiltonian_3_regular_graphs_are_1_connected
