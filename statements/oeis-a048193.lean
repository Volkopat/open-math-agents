import Mathlib

/-!
# A048193 and A079456

Sources: https://oeis.org/A048193 and https://oeis.org/A079456.
Sean A. Irvine conjectured that A048193 is the partial sum of A079456.
Andrei Zabolotskii observed that the complement of a chordal graph has at most
one connected component containing an edge.

The counts take isomorphism classes of graphs on `Fin n`. The sum over `i : Fin n`
uses `i.val + 1` as the index in A079456, whose offset is 1.
-/

namespace OMA.S_oeis_a048193

open SimpleGraph

/-- A chordal graph has no induced cycle of length at least four. -/
def Chordal {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, 4 ≤ k → ¬ (cycleGraph k).IsIndContained G

/-- Relabeling by an adjacency-preserving bijection identifies two graphs. -/
def graphIsoSetoid {V : Type} (P : SimpleGraph V → Prop) : Setoid {G // P G} where
  r G H := Nonempty (G.val ≃g H.val)
  iseqv := ⟨fun _ => ⟨SimpleGraph.Iso.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

abbrev ChordalClass (n : ℕ) :=
  Quotient (graphIsoSetoid (V := Fin n) Chordal)

abbrev ConnectedCochordalClass (n : ℕ) :=
  Quotient (graphIsoSetoid (V := Fin n) (fun G => G.Connected ∧ Chordal Gᶜ))

noncomputable def a (n : ℕ) : ℕ := Nat.card (ChordalClass n)

noncomputable def b (n : ℕ) : ℕ := Nat.card (ConnectedCochordalClass n)

theorem main : ∀ n : ℕ, 1 ≤ n → a n = ∑ i : Fin n, b (i.val + 1) := by
  sorry

end OMA.S_oeis_a048193
