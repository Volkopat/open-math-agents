import Mathlib

/-!
# Half-integral flow polynomial values

Source: http://www.openproblemgarden.org/op/half_integral_flow_polynomial_values
Credit: @shc261392

Conjecture (Mohar). `Φ(G, 5.5) > 0` for every 2-edge-connected graph `G`, where `Φ(G, x)` is
the flow polynomial of `G` (for a positive integer `k`, `Φ(G, k)` is the number of nowhere-zero
`k`-flows of `G`).

Reading used here:
* A finite multigraph is given by finite types `V`, `E` and `ends : E → Sym2 V`; parallel edges
  and loops are allowed (a loop multiplies the flow polynomial by `x - 1`).
* 2-edge-connected: `V` is nonempty, the multigraph is connected, and it has no bridge, i.e. the
  ends of every edge stay joined by a walk avoiding that edge.
* The flow polynomial is evaluated through the standard subset expansion
  `Φ(G, x) = ∑_{A ⊆ E} (-1)^{|E| - |A|} x^{|A| - |V| + c(A)}`, where `c(A)` is the number of
  connected components of the spanning subgraph `(V, A)`; the exponent is the nullity of `A`,
  which is never negative.
-/

namespace OMA.S_opg_half_integral_flow_polynomial_values

/-- The simple graph on `V` recording which vertices are joined by an edge of `A`. -/
def spanning {V E : Type*} (ends : E → Sym2 V) (A : Finset E) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ e ∈ A, ends e = s(u, v)

/-- The flow polynomial of the multigraph `ends`, evaluated at the real number `x`. -/
noncomputable def flowPoly {V E : Type*} [Fintype V] [Fintype E] (ends : E → Sym2 V) (x : ℝ) :
    ℝ :=
  ∑ A ∈ (Finset.univ : Finset E).powerset,
    (-1 : ℝ) ^ (Fintype.card E - A.card) *
      x ^ (A.card + Nat.card (spanning ends A).ConnectedComponent - Fintype.card V)

theorem main :
    ∀ (V E : Type) [Fintype V] [Fintype E] (ends : E → Sym2 V),
      Nonempty V →
      (∀ u v : V, Relation.ReflTransGen (fun a b => ∃ e, ends e = s(a, b)) u v) →
      (∀ (e : E) (u v : V), ends e = s(u, v) →
        Relation.ReflTransGen (fun a b => ∃ e', e' ≠ e ∧ ends e' = s(a, b)) u v) →
      0 < flowPoly ends (11 / 2) := by
  sorry

end OMA.S_opg_half_integral_flow_polynomial_values
