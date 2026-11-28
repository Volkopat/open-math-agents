import Mathlib

/-!
# Beneš Conjecture (graph-theoretic form)

Source: https://www.openproblemgarden.org/op/bene_conjecture_graph_theoretic_form_0
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (◇): let `L` be a simple regular ordered 2-stage graph. If `L^m` is externally
connected for some `m ≥ 1`, then `L^{2m}` is rearrangeable.

Encoding. A regular ordered 2-stage graph has parts of equal size `n` (regularity forces
this), so both parts are `Fin n` with their natural order; simplicity means at most one edge
between two vertices, so `L` is a relation `adj : Fin n → Fin n → Prop`, and regularity means
every vertex on either side has the same degree `d`. The proper concatenation `L^k` of `k`
copies has parts `V_0, …, V_k`, each a copy of `Fin n` (target `a` of one copy glued to
source `a` of the next, respecting the orders), and an edge `(i, a, b)` between `a ∈ V_i` and
`b ∈ V_{i+1}` whenever `adj a b`. A plain path is then a map `p : Fin (k+1) → Fin n` with
consecutive values adjacent. A mask is a 2-stage multigraph on sources and targets in which
every vertex has degree `d` (its degree in `L^k`); we index its edges by a finite type `E`.
A routing assigns to each mask edge a plain path between its endpoints, the paths being
mutually edge-disjoint.
-/

namespace OMA.S_opg_bene_conjecture_graph_theoretic_form_0

/-- `p` is a plain path of `L^k` (layers `0, …, k`). -/
def IsPlainPath {n : ℕ} (adj : Fin n → Fin n → Prop) (k : ℕ) (p : Fin (k + 1) → Fin n) :
    Prop :=
  ∀ i : Fin k, adj (p i.castSucc) (p i.succ)

/-- `L^k` is externally connected: every source is joined to every target by a plain path. -/
def ExternallyConnected {n : ℕ} (adj : Fin n → Fin n → Prop) (k : ℕ) : Prop :=
  ∀ s t : Fin n, ∃ p : Fin (k + 1) → Fin n,
    IsPlainPath adj k p ∧ p 0 = s ∧ p (Fin.last k) = t

/-- `L^k` is rearrangeable, where every source and target of `L^k` has degree `d`: every mask
(a 2-stage multigraph on sources and targets, edges indexed by `E`, all degrees equal to `d`)
admits a routing by mutually edge-disjoint plain paths. -/
def Rearrangeable {n : ℕ} (adj : Fin n → Fin n → Prop) (d k : ℕ) : Prop :=
  ∀ (E : Type) [Fintype E] (src tgt : E → Fin n),
    (∀ a, Fintype.card {e // src e = a} = d) →
    (∀ b, Fintype.card {e // tgt e = b} = d) →
    ∃ P : E → Fin (k + 1) → Fin n,
      (∀ e, IsPlainPath adj k (P e) ∧ P e 0 = src e ∧ P e (Fin.last k) = tgt e) ∧
      ∀ e e', e ≠ e' → ∀ i : Fin k,
        (P e i.castSucc, P e i.succ) ≠ (P e' i.castSucc, P e' i.succ)

/-- Beneš conjecture, graph-theoretic form (◇). -/
theorem main :
    ∀ (n d : ℕ) (adj : Fin n → Fin n → Prop) [DecidableRel adj],
      (∀ a, (Finset.univ.filter fun b => adj a b).card = d) →
      (∀ b, (Finset.univ.filter fun a => adj a b).card = d) →
      ∀ m : ℕ, 1 ≤ m → ExternallyConnected adj m →
        Rearrangeable adj d (2 * m) := by
  sorry

end OMA.S_opg_bene_conjecture_graph_theoretic_form_0
