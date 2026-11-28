import Mathlib

/-!
# Packing T-joins

Source: http://www.openproblemgarden.org/op/packing_t_joins
Credit: @shc261392

Conjecture (DeVos and Seymour). There exists a fixed constant `c` so that every graft with
minimum `T`-cut size at least `k` contains a `T`-join packing of size at least `(2/3)k - c`.

Reading used here:
* A graft is a finite loopless multigraph (`ends : E → Sym2 V`, parallel edges allowed) with a
  set `T ⊆ V` of even size.
* For `X ⊆ V`, the edge cut `δ(X)` is the set of edges with exactly one end in `X`; it is a
  `T`-cut when `|X ∩ T|` is odd.
* A `T`-join is a set `S` of edges such that a vertex has odd degree in `(V, S)` exactly when it
  lies in `T`; a `T`-join packing is a family of pairwise disjoint `T`-joins.
* The constant `c` is a natural number, the same for all grafts and all `k`.
-/

namespace OMA.S_opg_packing_t_joins

open Classical in
/-- The edge cut `δ(X)`: edges with exactly one end in `X`. -/
noncomputable def cutSet {V E : Type*} [Fintype E] (ends : E → Sym2 V) (X : Finset V) :
    Finset E :=
  Finset.univ.filter fun e => ∃ a b, ends e = s(a, b) ∧ a ∈ X ∧ b ∉ X

open Classical in
/-- `S` is a `T`-join: the odd-degree vertices of `(V, S)` are exactly those in `T`. -/
def IsTJoin {V E : Type*} (ends : E → Sym2 V) (T : Finset V) (S : Finset E) : Prop :=
  ∀ v, Odd (S.filter fun e => v ∈ ends e).card ↔ v ∈ T

theorem main :
    ∃ c : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] (ends : E → Sym2 V),
      (∀ e, ¬ (ends e).IsDiag) →
      ∀ T : Finset V, Even T.card →
      ∀ k : ℕ, (∀ X : Finset V, Odd (X ∩ T).card → k ≤ (cutSet ends X).card) →
        ∃ (m : ℕ) (S : Fin m → Finset E), (∀ i, IsTJoin ends T (S i)) ∧
          Pairwise (fun i j => Disjoint (S i) (S j)) ∧ (2 / 3 : ℝ) * k - c ≤ m := by
  sorry

end OMA.S_opg_packing_t_joins
