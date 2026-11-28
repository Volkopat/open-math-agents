import Mathlib

/-!
# Graceful difference labelings of disjoint unions of circuits

Source: https://arxiv.org/abs/1908.11300 (Hertz, Picouleau), the conjecture of the abstract and
Section 2: all disjoint unions of circuits have a gdl, except C⃗₃ and C⃗₂ + C⃗₃ (which have none).

A graceful difference labeling (gdl) of a directed graph with vertex set V is a bijection
f : V → {1, …, |V|} such that the difference labels f(v) − f(u) of the arcs uv are distinct.
The circuit C⃗ₖ (k ≥ 2) has vertices v₁, …, vₖ and arcs vᵢvᵢ₊₁ and vₖv₁. A disjoint union of
circuits is given by the list ks of its circuit lengths; its vertices are pairs (i, j) with
j : Fin ks[i], and each vertex has exactly one out-arc, to its successor on its circuit, so arcs
correspond to their tails. Labels are taken in Fin |V| (that is, 0, …, |V| − 1), which shifts all
labels by one and leaves the differences unchanged.

Literature: the paper proves the case with at most one odd circuit and the case with no odd
circuit of length ≥ 5; the remaining case (at least two odd circuits, one of length ≥ 5) is open,
and no later resolution was found.
-/

namespace OMA.S_arxiv_1908_11300

/-- The vertices of the disjoint union of circuits of lengths `ks`. -/
abbrev Vert (ks : List ℕ) : Type := Σ i : Fin ks.length, Fin ks[i]

/-- The head of the unique arc leaving a vertex: its successor on its circuit. -/
def next {ks : List ℕ} (v : Vert ks) : Vert ks := ⟨v.1, finRotate _ v.2⟩

/-- The union of circuits of lengths `ks` has a graceful difference labeling. -/
def HasGDL (ks : List ℕ) : Prop :=
  ∃ f : Vert ks ≃ Fin (Fintype.card (Vert ks)),
    Function.Injective fun v => ((f (next v) : ℕ) : ℤ) - (f v : ℕ)

theorem main : ∀ ks : List ℕ, (∀ k ∈ ks, 2 ≤ k) →
    (HasGDL ks ↔ ¬ ((ks : Multiset ℕ) = {3} ∨ (ks : Multiset ℕ) = {2, 3})) := by
  sorry

end OMA.S_arxiv_1908_11300
