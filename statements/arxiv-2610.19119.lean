import Mathlib

namespace OMA.S_arxiv_2610_19119

/-- The `j`-th Catalan number `C_j = (1 / (j + 1)) * C(2j, j)`. -/
def catalanNum (j : ℕ) : ℕ :=
  Nat.choose (2 * j) j / (j + 1)

/-- A directed edge `i → j` with `i < j` on vertex set `Fin m`. -/
abbrev DirEdge (m : ℕ) := { e : Fin m × Fin m // e.1 < e.2 }

/-- The indegree of vertex `i` in a directed multigraph `G` (represented as a list of
    directed edges with parallel edges distinguished by index). -/
def multigraphIndeg {m : ℕ} (G : List (DirEdge m)) (i : Fin m) : ℕ :=
  (Finset.univ.filter fun idx : Fin G.length => (G.get idx).val.2 = i).card

/-- Nonnegative integer flows `F(G)` on a directed multigraph `G` on `Fin m` with one exit
    at each vertex to a common sink: edge flows `f_e ≥ 0` and exit flows `b_i ≥ 0` satisfying
    `b_i + ∑_{e : i → *} f_e = indeg_G(i) + ∑_{e : * → i} f_e` for every `i : Fin m`. -/
abbrev GraphFlow {m : ℕ} (G : List (DirEdge m)) : Type :=
  { fb : (Fin G.length → ℕ) × (Fin m → ℕ) //
    ∀ i : Fin m,
      fb.2 i + ∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length => (G.get idx).val.1 = i), fb.1 idx =
      multigraphIndeg G i +
        ∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length => (G.get idx).val.2 = i), fb.1 idx }

/-- Complete reduction tree rooted at a directed multigraph `G` under Postnikov's reduction rule
    `x_{ij} x_{jk} ↦ x_{ij} x_{ik} + x_{ik} x_{jk}` (`i < j < k`).
    At each internal step, two edges `p : i → j` and `q : j → k` are replaced by `(i → j, i → k)`
    in the left child and `(i → k, j → k)` in the right child; leaves are terminal multigraphs
    where no vertex has both an incoming and an outgoing edge. -/
inductive RedTree (m : ℕ) : List (DirEdge m) → Type
  | leaf (G : List (DirEdge m))
      (hterm : ∀ e₁ ∈ G, ∀ e₂ ∈ G, e₁.val.2 ≠ e₂.val.1) : RedTree m G
  | step (G : List (DirEdge m)) (p q : Fin G.length)
      (hne : p ≠ q) (hchain : (G.get p).val.2 = (G.get q).val.1)
      (left : RedTree m
        (G.set q.val ⟨((G.get p).val.1, (G.get q).val.2),
          lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩))
      (right : RedTree m
        (G.set p.val ⟨((G.get p).val.1, (G.get q).val.2),
          lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩)) :
      RedTree m G

/-- Number of leaves (counted with multiplicity) of a complete reduction tree. -/
def RedTree.leaves {m : ℕ} : {G : List (DirEdge m)} → RedTree m G → ℕ
  | _, .leaf _ _ => 1
  | _, .step _ _ _ _ _ l r => l.leaves + r.leaves

/-- Edge list of the complete directed graph `K_m` on `Fin m` with all edges `i → j` (`i < j`). -/
def completeEdges (m : ℕ) : List (DirEdge m) :=
  (List.finRange m).flatMap fun i =>
    (List.finRange m).filterMap fun j =>
      if h : i < j then some ⟨(i, j), h⟩ else none

/-- Two-exit integer flows `A_{m,k}` on `K_m` (Section 3): arrays `(f_{ij}, b_i, r_i)` of
    nonnegative integers satisfying
    `b_i + r_i + ∑_{j > i} f_{ij} = i + ∑_{h < i} f_{hi}` for all `i : Fin m`
    (indexing `Fin m = {0, ..., m-1}`, so `indeg_{K_m}(i) = i`),
    with exactly `k` active vertices (`r_i > 0`). -/
abbrev TwoExitFlow (m k : ℕ) : Type :=
  { fbr : (DirEdge m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ) //
    (∀ i : Fin m,
      fbr.2.1 i + fbr.2.2 i +
        ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1 = i), fbr.1 e =
      i.val + ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2 = i), fbr.1 e) ∧
    (Finset.univ.filter fun i : Fin m => 0 < fbr.2.2 i).card = k }

/-- Marked flows on the left-hand side of Proposition 5.1: `(F, P)` with `F ∈ A_{m,k}`
    and `P` a 2-element subset of `S(F) ∪ {∞}` (`none` denotes the sink `∞`). -/
def LeftMarkedFlow (m k : ℕ) : Type :=
  { x : TwoExitFlow m k × Finset (Option (Fin m)) //
    x.2.card = 2 ∧
    ∀ u ∈ x.2, match u with
      | none => True
      | some i => 0 < x.1.val.2.2 i }

/-- Marked flows on the right-hand side of Proposition 5.1: `(F, P)` with `F ∈ A_{m,k-1}`
    and `P` a 2-element subset of `[m] \ S(F)`. -/
def RightMarkedFlow (m k : ℕ) : Type :=
  { y : TwoExitFlow m (k - 1) × Finset (Fin m) //
    y.2.card = 2 ∧ ∀ i ∈ y.2, y.1.val.2.2 i = 0 }

/-- Combinatorial proof of the Chan–Robbins–Yuen volume formula, Postnikov's reduction formula,
    and the Morales–Shi recurrence (arXiv:2610.19119, Theorems 1.1–1.2, Lemmas 2.1, 3.1, 4.1,
    Proposition 5.1):
    1. For every directed multigraph `G` on `Fin m`, `GraphFlow G` is finite, a complete
       reduction tree rooted at `G` exists, and every complete reduction tree `T` rooted at `G`
       has `T.leaves = Nat.card (GraphFlow G)` (Lemma 2.1).
    2. For `1 ≤ k ≤ m - 1`, `LeftMarkedFlow m k ≃ RightMarkedFlow m k` (Proposition 5.1) and
       `C(k + 1, 2) * |A_{m,k}| = C(m - k + 1, 2) * |A_{m,k-1}|` (Lemma 3.1).
    3. Narayana refinement: for `m ≥ 1` and `k ≤ m - 1`,
       `m * |A_{m,k}| = |F(K_m)| * C(m, k) * C(m, k + 1)`.
    4. Vertex-deletion bijection: for `m ≥ 1`,
       `A_{m+1,m} ≃ Σ k : Fin m, A_{m,k}` (Lemma 4.1).
    5. Postnikov's reduction formula & CRY volume integer-flow count: for every `m ≥ 1`,
       `|F(K_m)| = ∏_{j=1}^{m-1} C_j`, and every complete reduction tree `T` rooted at `K_m`
       has `T.leaves = ∏_{j=1}^{m-1} C_j` (Theorems 1.1 & 1.2). -/
theorem main :
    (∀ (m : ℕ) (G : List (DirEdge m)),
      Finite (GraphFlow G) ∧
      Nonempty (RedTree m G) ∧
      ∀ T : RedTree m G, T.leaves = Nat.card (GraphFlow G)) ∧
    (∀ (m k : ℕ), 1 ≤ k → k ≤ m - 1 →
      Nonempty (LeftMarkedFlow m k ≃ RightMarkedFlow m k) ∧
      Nat.choose (k + 1) 2 * Nat.card (TwoExitFlow m k) =
        Nat.choose (m - k + 1) 2 * Nat.card (TwoExitFlow m (k - 1))) ∧
    (∀ (m k : ℕ), 1 ≤ m → k ≤ m - 1 →
      m * Nat.card (TwoExitFlow m k) =
        Nat.card (GraphFlow (completeEdges m)) * Nat.choose m k * Nat.choose m (k + 1)) ∧
    (∀ m : ℕ, 1 ≤ m →
      Nonempty (TwoExitFlow (m + 1) m ≃ (k : Fin m) × TwoExitFlow m k.val)) ∧
    (∀ m : ℕ, 1 ≤ m →
      Nat.card (GraphFlow (completeEdges m)) = ∏ j ∈ Finset.Ico 1 m, catalanNum j ∧
      ∀ T : RedTree m (completeEdges m), T.leaves = ∏ j ∈ Finset.Ico 1 m, catalanNum j) := by
  sorry

end OMA.S_arxiv_2610_19119
