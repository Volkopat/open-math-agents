import Mathlib

namespace OMA.S_arxiv_2507_08483

/-- A list has no two consecutive equal elements. -/
def NoAdjEq {α : Type*} : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => a ≠ b ∧ NoAdjEq (b :: t)

/-- Two letters `x` and `y` alternate in a word `w` if, after deleting all other
letters from `w`, no two consecutive remaining letters are equal. -/
def Alternates {V : Type*} [DecidableEq V] (w : List V) (x y : V) : Prop :=
  NoAdjEq (w.filter (fun z => decide (z = x ∨ z = y)))

/-- A finite graph `G` on `V` is word-representable if there exists a word `w`
over `V` containing every vertex of `V` such that distinct vertices `x, y` are
adjacent in `G` iff `x` and `y` alternate in `w`. -/
def IsWordRepresentable {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ w : List V, (∀ v : V, v ∈ w) ∧ ∀ x y : V, x ≠ y → (G.Adj x y ↔ Alternates w x y)

/-- A finite graph `G` is a split graph with an independent set of size 4 if its
vertex set partitions into an independent set `E` of size 4 and a clique `K`. -/
def IsSplitGraphWithIndep4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (E K : Finset V),
    E.card = 4 ∧ Disjoint E K ∧ E ∪ K = Finset.univ ∧
    (∀ u ∈ E, ∀ v ∈ E, ¬ G.Adj u v) ∧
    (∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v)

/-- `H` occurs as an induced subgraph of `G`. -/
def HasInducedSubgraph {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : W ↪ V, ∀ u v : W, H.Adj u v ↔ G.Adj (f u) (f v)

/-- Helper constructor for a split graph on `e + k` vertices, where `0..e-1` form
an independent set, `e..e+k-1` form a clique, and bit `i` of `cols[j]` indicates
adjacency between independent vertex `i` and clique vertex `e + j`. -/
def mkSplitGraph (e k : ℕ) (cols : List ℕ) : SimpleGraph (Fin (e + k)) where
  Adj u v :=
    u ≠ v ∧
    ((e ≤ u.val ∧ e ≤ v.val) ∨
     (u.val < e ∧ e ≤ v.val ∧ ((cols.getD (v.val - e) 0) >>> u.val) % 2 = 1) ∨
     (v.val < e ∧ e ≤ u.val ∧ ((cols.getD (u.val - e) 0) >>> v.val) % 2 = 1))
  symm := ⟨by
    intro u v ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with ⟨h1, h2⟩ | h | h
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Minimal forbidden induced split graphs `T_1, ..., T_8` and `D_1`
(Kitaev–Long–Ma–Wu, Chen–Kitaev–Saito, and Roy–Hariharasubramanian). -/
def graphT1 : SimpleGraph (Fin (3 + 4)) := mkSplitGraph 3 4 [5, 3, 6, 0]
def graphT2 : SimpleGraph (Fin (3 + 4)) := mkSplitGraph 3 4 [7, 1, 2, 4]
def graphT3 : SimpleGraph (Fin (3 + 4)) := mkSplitGraph 3 4 [5, 3, 7, 6]
def graphT4 : SimpleGraph (Fin (4 + 4)) := mkSplitGraph 4 4 [9, 3, 15, 6]
def graphT5 : SimpleGraph (Fin (4 + 5)) := mkSplitGraph 4 5 [9, 3, 6, 12, 0]
def graphT6 : SimpleGraph (Fin (4 + 5)) := mkSplitGraph 4 5 [1, 11, 7, 4, 8]
def graphT7 : SimpleGraph (Fin (4 + 5)) := mkSplitGraph 4 5 [9, 3, 5, 10, 12]
def graphT8 : SimpleGraph (Fin (4 + 5)) := mkSplitGraph 4 5 [11, 7, 9, 5, 2]
def graphD1 : SimpleGraph (Fin (4 + 6)) := mkSplitGraph 4 6 [3, 2, 5, 4, 9, 8]

/-- Roy–Hariharasubramanian (arXiv:2507.08483, Theorem 3.1), solving the open
problem of Kitaev and Pyatkin: a split graph with an independent set of size 4
is word-representable if and only if it contains none of `T_1, ..., T_8, D_1` as
an induced subgraph. -/
theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsSplitGraphWithIndep4 G →
      (IsWordRepresentable G ↔
        ¬ HasInducedSubgraph G graphT1 ∧
        ¬ HasInducedSubgraph G graphT2 ∧
        ¬ HasInducedSubgraph G graphT3 ∧
        ¬ HasInducedSubgraph G graphT4 ∧
        ¬ HasInducedSubgraph G graphT5 ∧
        ¬ HasInducedSubgraph G graphT6 ∧
        ¬ HasInducedSubgraph G graphT7 ∧
        ¬ HasInducedSubgraph G graphT8 ∧
        ¬ HasInducedSubgraph G graphD1) := by sorry

end OMA.S_arxiv_2507_08483
