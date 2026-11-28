import Mathlib

namespace OMA.S_arxiv_2611_19659

/-- An interior diagonal of the convex `n`-gon with vertices `0, 1, ..., n - 1` in cyclic order. -/
abbrev TriDiag (n : ℕ) : Type :=
  { p : Fin n × Fin n // p.1.val + 1 < p.2.val ∧ ¬ (p.1.val = 0 ∧ p.2.val = n - 1) }

/-- Two interior diagonals cross iff their endpoints alternate strictly in cyclic order. -/
def DiagsCross {n : ℕ} (d₁ d₂ : TriDiag n) : Prop :=
  (d₁.val.1 < d₂.val.1 ∧ d₂.val.1 < d₁.val.2 ∧ d₁.val.2 < d₂.val.2) ∨
  (d₂.val.1 < d₁.val.1 ∧ d₁.val.1 < d₂.val.2 ∧ d₂.val.2 < d₁.val.2)

/-- A triangulation of the convex `n`-gon: a set of `n - 3` pairwise noncrossing diagonals. -/
abbrev Triangulation (n : ℕ) : Type :=
  { T : Finset (TriDiag n) // T.card = n - 3 ∧ ∀ d₁ ∈ T, ∀ d₂ ∈ T, ¬ DiagsCross d₁ d₂ }

/-- Adjacency in the associahedron flip graph `𝒜_n`: replacing a single diagonal. -/
def FlipAdj {n : ℕ} (T₁ T₂ : Triangulation n) : Prop :=
  (T₁.val \ T₂.val).card = 1 ∧ (T₂.val \ T₁.val).card = 1

/-- Ordered full binary trees (every vertex has either 0 or 2 children). -/
inductive FullBinTree : Type
  | leaf : FullBinTree
  | node : FullBinTree → FullBinTree → FullBinTree
  deriving DecidableEq

/-- Number of leaves of an ordered full binary tree. -/
def FullBinTree.leaves : FullBinTree → ℕ
  | .leaf => 1
  | .node l r => l.leaves + r.leaves

/-- Adjacency in the rotation graph of ordered full binary trees:
    a single local rotation `((U, V), W) ↔ (U, (V, W))` at some rooted subtree. -/
inductive RotAdj : FullBinTree → FullBinTree → Prop
  | rotRight (u v w : FullBinTree) :
      RotAdj (.node (.node u v) w) (.node u (.node v w))
  | rotLeft (u v w : FullBinTree) :
      RotAdj (.node u (.node v w)) (.node (.node u v) w)
  | inLeft {l l' r : FullBinTree} :
      RotAdj l l' → RotAdj (.node l r) (.node l' r)
  | inRight {l r r' : FullBinTree} :
      RotAdj r r' → RotAdj (.node l r) (.node l r')

/-- Recursive bottom-up labelling of a full binary tree using a binary operation `op`
    with leaf label `x`. -/
def evalBinTree {S : Type*} (op : S → S → S) (x : S) : FullBinTree → S
  | .leaf => x
  | .node l r => op (evalBinTree op x l) (evalBinTree op x r)

/-- A binary operation `op` on `S` forms a quasigroup iff every left and right translation
    is bijective. -/
def IsQuasigroup {S : Type*} (op : S → S → S) : Prop :=
  (∀ a : S, Function.Bijective (op a)) ∧ (∀ b : S, Function.Bijective (fun a => op a b))

/-- David R. Wood, *Associahedra are 8-colourable* (`arXiv:2611.19659`):
    1. (Theorem 1) For every `n ≥ 3`, the associahedron graph `𝒜_n` (on triangulations of a
       convex `n`-gon, and equivalently on ordered full binary trees with `n - 1` leaves)
       is `8`-colourable: `χ(𝒜_n) ≤ 8`.
    2. (Theorem 2) For any finite quasigroup `(S, op)`, leaf label `x ∈ S`, and parity function
       `β : FullBinTree → Bool`, if `T ↦ (λ(T), β(T))` properly colours `𝒜_n` for all `n ≥ 3`,
       then at least `4` labels are realised (`|S'| ≥ 4`), so `|S' × 𝔽₂| ≥ 8`. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n →
      ∃ c : Triangulation n → Fin 8,
        ∀ T₁ T₂ : Triangulation n, FlipAdj T₁ T₂ → c T₁ ≠ c T₂) ∧
    (∀ n : ℕ, 3 ≤ n →
      ∃ c : { T : FullBinTree // T.leaves = n - 1 } → Fin 8,
        ∀ T₁ T₂ : { T : FullBinTree // T.leaves = n - 1 },
          RotAdj T₁.val T₂.val → c T₁ ≠ c T₂) ∧
    (∀ (S : Type) [Fintype S] (op : S → S → S) (x : S) (β : FullBinTree → Bool),
      IsQuasigroup op →
      (∀ n : ℕ, 3 ≤ n →
        ∀ T₁ T₂ : FullBinTree, T₁.leaves = n - 1 → T₂.leaves = n - 1 →
          RotAdj T₁ T₂ → (evalBinTree op x T₁, β T₁) ≠ (evalBinTree op x T₂, β T₂)) →
      4 ≤ (Set.range (evalBinTree op x)).ncard) := by
  sorry

end OMA.S_arxiv_2611_19659
