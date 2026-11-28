import FormalConjectures.ErdosProblems.«60»

/-!
# Two copies of the four-cycle above the extremal number

Deleting one edge per copy settles the case of edge excess at least two.
In the remaining case, a single deletion leaves an extremal four-cycle-free
graph. The structural question is whether each missing edge in such a graph
has two distinct three-edge paths between its endpoints.
-/

namespace OMA.R_Erdos60_erdos_60_variants_two_copies_R1

open SimpleGraph Filter

/-- A missing edge of an extremal four-cycle-free graph has at least two
oriented edges from the neighborhood of its first endpoint to that of its second. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
    (cycleGraph 4).Free F → F.edgeSet.ncard = extremalNumber n (cycleGraph 4) →
    ∀ u v : Fin n, u ≠ v → ¬ F.Adj u v →
      2 ≤ (Finset.univ.filter fun p : Fin n × Fin n =>
        F.Adj u p.1 ∧ F.Adj p.1 p.2 ∧ F.Adj p.2 v).card

/-- Closing a missing edge turns the three-edge paths with fixed, ordered
endpoints into distinct unlabelled four-cycles in any supergraph containing that edge. -/
def H2 : Prop :=
  ∀ (n : ℕ) (F G : SimpleGraph (Fin n)) [DecidableRel F.Adj],
    F ≤ G → ∀ u v : Fin n, ¬ F.Adj u v → G.Adj u v →
      (Finset.univ.filter fun p : Fin n × Fin n =>
        F.Adj u p.1 ∧ F.Adj p.1 p.2 ∧ F.Adj p.2 v).card ≤ G.copyCount (cycleGraph 4)

lemma ncard_eq_filter_card {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred q]
    (h : ∀ a, p a ↔ q a) :
    {a | p a}.ncard = (Finset.univ.filter q).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  apply congrArg Finset.card
  ext a
  simpa only [Set.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_filter_univ] using h a

lemma cycleCount {V W : Type*} [Fintype V] (G : SimpleGraph V) (H : SimpleGraph W) :
    {S : G.Subgraph | Nonempty (S.coe ≃g H)}.ncard = G.copyCount H := by
  classical
  unfold SimpleGraph.copyCount
  apply ncard_eq_filter_card
  intro S
  exact ⟨fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ => ⟨e.symm⟩⟩

lemma edgeCount {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = G.edgeFinset.card := Set.ncard_eq_toFinset_card' _

theorem main : H1 → H2 → type_of% @Erdos60.erdos_60.variants.two_copies := by
  intro structural closePath
  filter_upwards [structural] with n hstruct
  intro G _ excess
  classical
  rw [cycleCount]
  by_contra! few
  let F := G.killCopies (cycleGraph 4)
  have nonemptyCycle : cycleGraph 4 ≠ ⊥ := by
    intro h
    have adj : (cycleGraph 4).Adj 0 1 := by decide
    rw [h] at adj
    exact adj
  have free : (cycleGraph 4).Free F := free_killCopies nonemptyCycle
  have upper := card_edgeFinset_le_extremalNumber free
  rw [← edgeCount, Fintype.card_fin] at upper
  have lower : G.edgeFinset.card - G.copyCount (cycleGraph 4) ≤ F.edgeFinset.card :=
    le_card_edgeFinset_killCopies
  rw [← edgeCount, ← edgeCount] at lower
  rw [← edgeCount] at excess
  have extremal : F.edgeSet.ncard = extremalNumber n (cycleGraph 4) := by omega
  have sub : F ≤ G := killCopies_le_left
  have missing : ∃ u v, G.Adj u v ∧ ¬ F.Adj u v := by
    by_contra! allEdges
    have eq : F = G := le_antisymm sub allEdges
    rw [eq] at upper
    omega
  obtain ⟨u, v, huv, hmissing⟩ := missing
  exact (not_le_of_gt few) <| (hstruct F free extremal u v huv.ne hmissing).trans
    (closePath n F G sub u v hmissing huv)

end OMA.R_Erdos60_erdos_60_variants_two_copies_R1
