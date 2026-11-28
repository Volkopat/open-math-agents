import Mathlib

/-!
# Bounds on numbers of matchings of given sizes in bipartite graphs

Source: https://mathoverflow.net/questions/88547
Credit: @LDJAI

A simple bipartite graph is represented by its finite edge set between two
labelled parts. The requested classification is encoded via the size of a
vertex cover and multiplicities of the possible neighborhoods outside it.
A bound on those multiplicities makes the classification a finite search.
-/

namespace OMA.S_mo_88547

/-- Count size-`i` edge sets whose endpoints are distinct on both sides. -/
def matchingCount {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (i : ℕ) : ℕ :=
  ((E.powersetCard i).filter fun M =>
    (M.image Prod.fst).card = i ∧ (M.image Prod.snd).card = i).card

def realizes {A B : Type} [DecidableEq A] [DecidableEq B] {k : ℕ}
    (E : Finset (A × B)) (m : Fin k → ℕ) : Prop :=
  (∀ i : Fin k, matchingCount E (i.val + 1) = m i) ∧ matchingCount E (k + 1) = 0

/-- Apart from the given core edges, an edge joins a core vertex to a vertex
of the opposite part whose neighborhood contains it. -/
def coverEdges {a b : ℕ} (H : Finset (Fin a × Fin b))
    (p : Finset (Fin a) → ℕ) (q : Finset (Fin b) → ℕ) :
    Finset ((Fin a ⊕ (Σ S : Finset (Fin b), Fin (q S))) ×
            (Fin b ⊕ (Σ S : Finset (Fin a), Fin (p S)))) :=
  Finset.univ.filter fun e =>
    (match e.1, e.2 with
    | Sum.inl u, Sum.inl v => decide ((u, v) ∈ H)
    | Sum.inl u, Sum.inr v => decide (u ∈ v.1)
    | Sum.inr u, Sum.inl v => decide (v ∈ u.1)
    | Sum.inr _, Sum.inr _ => false) = true

/-- For a nonempty positive list, a graph exists exactly when one of the
finitely many cover patterns and bounded multiplicity vectors works.
The empty list corresponds to the empty graph. -/
theorem main : ∀ (k : ℕ) (m : Fin (k + 1) → ℕ), (∀ i, 0 < m i) →
    ((∃ (a b : ℕ) (E : Finset (Fin a × Fin b)), realizes E m) ↔
      ∃ (a b : ℕ) (H : Finset (Fin a × Fin b))
        (p : Finset (Fin a) → ℕ) (q : Finset (Fin b) → ℕ),
        a + b = k + 1 ∧ p ∅ = 0 ∧ q ∅ = 0 ∧
        (∀ S, p S ≤ m 0) ∧ (∀ S, q S ≤ m 0) ∧ realizes (coverEdges H p q) m) := by
  sorry

end OMA.S_mo_88547
