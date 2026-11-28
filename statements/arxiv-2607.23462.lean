import Mathlib

namespace OMA.S_arxiv_2607_23462

/-- The triangular prism graph `K_3 □ K_2` on 6 vertices (`0,1,2` and `3,4,5` form two triangles
joined by `0-3, 1-4, 2-5`). -/
def triangularPrism : SimpleGraph (Fin 6) where
  Adj u v :=
    (u ≠ v ∧ u.val / 3 = v.val / 3) ∨
    (u.val + 3 = v.val) ∨ (v.val + 3 = u.val)
  symm := ⟨by
    intro u v h
    rcases h with ⟨hne, hq⟩ | h1 | h2
    · exact Or.inl ⟨hne.symm, hq.symm⟩
    · exact Or.inr (Or.inr h1)
    · exact Or.inr (Or.inl h2)⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨hne, _⟩ | h1 | h2
    · exact hne rfl
    · omega
    · omega⟩

/-- A simple graph on `Fin n` is cubic (3-regular) if every vertex has degree 3. -/
def IsCubic {n : ℕ} (G : SimpleGraph (Fin n)) : Prop := by
  classical
  exact ∀ v : Fin n, G.degree v = 3

/-- A simple graph is claw-free if no vertex has three pairwise non-adjacent neighbors. -/
def IsClawFree {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v a b c : Fin n, G.Adj v a → G.Adj v b → G.Adj v c →
    a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

/-- A simple graph is diamond-free if no two triangles share an edge (`K_4 - e`-free). -/
def IsDiamondFree {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v x y : Fin n, G.Adj u v → G.Adj u x → G.Adj v x → G.Adj u y → G.Adj v y → x = y

/-- A strong `k`-edge-coloring assigns one of `k` colors to each edge so that every color class
is an induced matching (any two distinct edges of the same color are vertex-disjoint with no edge
joining their endpoints). -/
def IsStronglyEdgeColorable {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ c : Sym2 (Fin n) → Fin k,
    ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, e₁ ≠ e₂ → c e₁ = c e₂ →
      ∀ u ∈ e₁, ∀ v ∈ e₂, u ≠ v ∧ ¬ G.Adj u v

/-- Kardoš's conjecture (Problem 4.1, 33rd Workshop on Cycles and Colourings; disproved in
arXiv:2607.23462): every connected diamond-free claw-free cubic simple graph other than the
triangular prism is strongly 6-edge-colorable. -/
theorem main :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.Connected → IsCubic G → IsClawFree G → IsDiamondFree G →
      ¬ Nonempty (G ≃g triangularPrism) →
      IsStronglyEdgeColorable G 6 := by
  sorry

end OMA.S_arxiv_2607_23462
