import Mathlib

/-!
# Non-monochromatic triangles in k-edge-coloured graphs

Source: https://arxiv.org/abs/1809.10088, Conjectures 1.4 and 1.5
(Matt DeVos, Jessica McDonald and Amanda Montejano)
Credit: @pyaf

The paper proves that a simple graph G = (V, E) whose edges are partitioned
into R and B with |E| + min{|R|, |B|} > (|V| choose 2) has a triangle with
edges from both R and B, and conjectures two many-colour versions. Let
E = E₁ ⊔ ⋯ ⊔ E_k be a k-edge-colouring (colour classes may be empty).
* Conjecture 1.4: if 2|E| − max_i |E_i| > |V|²/2, then G has a
  non-monochromatic triangle.
* Conjecture 1.5: if |E_i| > |V|²/(4k − 2) for every 1 ≤ i ≤ k, then G has
  a non-monochromatic triangle.
Searches of arXiv for later work on non-monochromatic triangles and
coloured versions of Mantel's theorem found no resolution.

The inequalities are cleared of denominators. Only the colours of edges matter.
-/

namespace OMA.S_arxiv_1809_10088

/-- The number of edges of colour i. -/
def classSize {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (c : Sym2 V → Fin k) (i : Fin k) : ℕ :=
  (G.edgeFinset.filter (fun e => c e = i)).card

/-- Three pairwise adjacent vertices whose three edges do not all have the same colour. -/
def HasNonMonoTriangle {V : Type*} (G : SimpleGraph V) {k : ℕ} (c : Sym2 V → Fin k) : Prop :=
  ∃ a b d : V, G.Adj a b ∧ G.Adj b d ∧ G.Adj a d ∧
    ¬ (c s(a, b) = c s(b, d) ∧ c s(b, d) = c s(a, d))

theorem main :
    (∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
      (c : Sym2 V → Fin k),
      Fintype.card V ^ 2 + 2 * Finset.univ.sup (classSize G c) < 4 * G.edgeFinset.card →
      HasNonMonoTriangle G c) ∧
    (∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
      (c : Sym2 V → Fin k), 1 ≤ k →
      (∀ i, Fintype.card V ^ 2 < (4 * k - 2) * classSize G c i) →
      HasNonMonoTriangle G c) := by
  sorry

end OMA.S_arxiv_1809_10088
