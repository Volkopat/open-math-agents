import Mathlib

/-!
# Density of 3-flow-critical graphs

Source: https://arxiv.org/abs/2003.09162 (Li, Ma, Shi, Wang, Wu, On 3-flow-critical graphs),
the conjecture of the abstract and introduction: every 3-flow-critical graph on n ≥ 7 vertices has
at most 3n − 8 edges (tight for K₃,ₙ₋₃⁺ if true).

As in the paper, graphs are finite and may have parallel edges but no loops. A bridgeless graph G
is 3-flow-critical if G admits no nowhere-zero 3-flow but G/e has one for every edge e.
Conventions follow statements/opg-3-flow-conjecture.lean (helpers reused verbatim): a multigraph
is given by endpoint maps `tail head : E → V`, which also fix a reference orientation. An edge e is
a bridge when its ends are disconnected after deleting e. The contraction G/e is modelled on the
same vertex type: e is removed and every end equal to `head e` is redirected to `tail e`, which
leaves `head e` isolated; edges parallel to e become loops, and neither an isolated vertex nor a
loop affects the existence of a nowhere-zero flow, so this has a nowhere-zero 3-flow iff G/e does.

Literature: the paper proves 8n/5 − 2/5 ≤ |E(G)| ≤ 4n − 10 (hence the conjecture when many
vertices have degree 3); arXiv:2610.07034 (2026) still lists the 3n − 8 conjecture as open.
-/

namespace OMA.S_arxiv_2003_09162

/-- `u` and `w` are joined by an edge outside `S` (in either direction). -/
def AdjAvoiding {V E : Type} (tail head : E → V) (S : Finset E) (u w : V) : Prop :=
  ∃ e : E, e ∉ S ∧ ((tail e = u ∧ head e = w) ∨ (tail e = w ∧ head e = u))

/-- `f` is a nowhere-zero `k`-flow for the oriented multigraph `(tail, head)`. -/
def IsNowhereZeroFlow {V E : Type} [Fintype E] [DecidableEq V] (tail head : E → V)
    (k : ℕ) (f : E → ℤ) : Prop :=
  (∀ e, 0 < |f e| ∧ |f e| < k) ∧
  ∀ v : V, (∑ e ∈ Finset.univ.filter (fun e => head e = v), f e) =
    ∑ e ∈ Finset.univ.filter (fun e => tail e = v), f e

/-- No edge is a bridge: the ends of every edge stay connected after deleting it. -/
def Bridgeless {V E : Type} [DecidableEq E] (tail head : E → V) : Prop :=
  ∀ e : E, Relation.ReflTransGen (AdjAvoiding tail head {e}) (tail e) (head e)

/-- Redirect the vertex `head e` to `tail e`. -/
def merge {V E : Type} [DecidableEq V] (tail head : E → V) (e : E) (v : V) : V :=
  if v = head e then tail e else v

/-- `G/e` has a nowhere-zero 3-flow. -/
def ContractionHasFlow {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (tail head : E → V) (e : E) : Prop :=
  ∃ f : {x : E // x ≠ e} → ℤ,
    IsNowhereZeroFlow (fun x => merge tail head e (tail x.1))
      (fun x => merge tail head e (head x.1)) 3 f

/-- `G` is 3-flow-critical. -/
def IsThreeFlowCritical {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (tail head : E → V) : Prop :=
  Bridgeless tail head ∧ (¬ ∃ f, IsNowhereZeroFlow tail head 3 f) ∧
    ∀ e, ContractionHasFlow tail head e

theorem main :
    ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (tail head : E → V),
      (∀ e, tail e ≠ head e) → IsThreeFlowCritical tail head → 7 ≤ Fintype.card V →
      Fintype.card E ≤ 3 * Fintype.card V - 8 := by
  sorry

end OMA.S_arxiv_2003_09162
