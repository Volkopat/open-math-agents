import Mathlib

/-!
# Three 4-flows conjecture

Source: https://www.openproblemgarden.org/op/three_4_flows_conjecture
Credit: @shc261392

Conjecture (DeVos): for every graph `G` with no bridge, there exist three disjoint sets
`A₁, A₂, A₃ ⊆ E(G)` with `A₁ ∪ A₂ ∪ A₃ = E(G)` so that `G \ Aᵢ` has a nowhere-zero 4-flow for
`1 ≤ i ≤ 3`.

Reading used here:
* `G` is a finite loopless multigraph: a finite vertex type `V`, a finite edge type `E` and
  `ends : E → Sym2 V` with no loops. (Loops play no role for flows: a loop may carry any
  nonzero value.)
* An edge `e` with ends `u, v` is a bridge if `u` and `v` are not joined by a path avoiding
  `e`.
* The partition is given by a map `A : E → Fin 3`, with `Aᵢ = A⁻¹(i)` (some parts may be
  empty), and `G \ Aᵢ` is the spanning subgraph with edge set `{e | A e ≠ i}`.
* By Tutte's theorem the existence of a nowhere-zero `Γ`-flow depends only on `|Γ|`, so
  nowhere-zero 4-flows are taken in the Klein group `ZMod 2 × ZMod 2`, where orientation plays
  no role: values nonzero on the edge set, summing to zero at every vertex.
-/

namespace OMA.S_opg_three_4_flows_conjecture

open Classical in
/-- The spanning subgraph with edge set `F` has a nowhere-zero 4-flow (Klein group values). -/
def HasNZ4Flow {V E : Type} [Fintype E] [DecidableEq V] (ends : E → Sym2 V) (F : Set E) :
    Prop :=
  ∃ f : E → ZMod 2 × ZMod 2, (∀ e ∈ F, f e ≠ 0) ∧
    ∀ v : V, ∑ e ∈ Finset.univ.filter (fun e => v ∈ ends e), (if e ∈ F then f e else 0) = 0

/-- No edge is a bridge. -/
def Bridgeless {V E : Type} (ends : E → Sym2 V) : Prop :=
  ∀ e u v, ends e = s(u, v) →
    Relation.ReflTransGen (fun a b => ∃ e', e' ≠ e ∧ ends e' = s(a, b)) u v

theorem main :
    ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (ends : E → Sym2 V),
      (∀ e, ¬ (ends e).IsDiag) → Bridgeless ends →
        ∃ A : E → Fin 3, ∀ i : Fin 3, HasNZ4Flow ends {e | A e ≠ i} := by
  sorry

end OMA.S_opg_three_4_flows_conjecture
