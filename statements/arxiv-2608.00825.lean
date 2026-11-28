import Mathlib

namespace OMA.S_arxiv_2608_00825

/-- A loopless directed graph on vertex type `V`. -/
structure FinDigraph (V : Type*) where
  adj : V → V → Prop
  loopless : ∀ v, ¬ adj v v

/-- Directed walk of exact length `k` from `u` to `v` in `D`. -/
inductive ReachIn {V : Type*} (D : FinDigraph V) : ℕ → V → V → Prop
  | zero (u : V) : ReachIn D 0 u u
  | succ {k : ℕ} {u w v : V} : D.adj u w → ReachIn D k w v → ReachIn D (k + 1) u v

/-- `D` contains a directed cycle of length `ℓ ≥ 2`. -/
def HasDirCycle {V : Type*} (D : FinDigraph V) (ℓ : ℕ) : Prop :=
  2 ≤ ℓ ∧ ∃ f : Fin ℓ → V, Function.Injective f ∧
    ∀ i : Fin ℓ, D.adj (f i) (f ⟨(i.val + 1) % ℓ, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

/-- `D` has directed girth `ℓ`: it has a directed `ℓ`-cycle and no shorter directed cycle. -/
def DirectedGirth {V : Type*} (D : FinDigraph V) (ℓ : ℕ) : Prop :=
  HasDirCycle D ℓ ∧ ∀ ℓ', HasDirCycle D ℓ' → ℓ ≤ ℓ'

/-- `D` is strongly connected. -/
def IsStronglyConnected {V : Type*} (D : FinDigraph V) : Prop :=
  ∀ u v : V, ∃ k : ℕ, ReachIn D k u v

/-- `D` is weakly connected (its underlying undirected graph is connected). -/
def IsWeaklyConnected {V : Type*} (D : FinDigraph V) : Prop :=
  ∀ u v : V, Relation.ReflTransGen (fun x y => D.adj x y ∨ D.adj y x) u v

/-- `D` is source-free (every vertex has in-degree at least `1`). -/
def IsSourceFree {V : Type*} (D : FinDigraph V) : Prop :=
  ∀ v : V, ∃ u : V, D.adj u v

/-- `c : V → Bool` is a proper 2-coloring (bipartition) of the underlying graph of `D`. -/
def IsBipartition {V : Type*} (D : FinDigraph V) (c : V → Bool) : Prop :=
  ∀ u v : V, D.adj u v → c u ≠ c v

/-- `D` is bipartite. -/
def IsBipartite {V : Type*} (D : FinDigraph V) : Prop :=
  ∃ c : V → Bool, IsBipartition D c

/-- `Q` is an independent set in `D`. -/
def IsIndependent {V : Type*} (D : FinDigraph V) (Q : Finset V) : Prop :=
  ∀ u ∈ Q, ∀ v ∈ Q, ¬ D.adj u v

/-- `Q` is a `q`-kernel of `D`: independent and every vertex is reachable from `Q` in at most `q` steps. -/
def IsQKernel {V : Type*} (D : FinDigraph V) (q : ℕ) (Q : Finset V) : Prop :=
  IsIndependent D Q ∧ ∀ v : V, ∃ u ∈ Q, ∃ k ≤ q, ReachIn D k u v

/-- `D` contains a spanning out-arborescence (out-branching) rooted at some vertex `r`. -/
def HasOutBranching {V : Type*} (D : FinDigraph V) : Prop :=
  ∃ (r : V) (parent : V → V),
    (∀ v, v ≠ r → D.adj (parent v) v) ∧
    (∀ v : V, ∃ k : ℕ, parent^[k] v = r)

/-- `D` is unicyclic: every vertex has in-degree exactly `1` and the underlying graph is connected. -/
def IsUnicyclic {V : Type*} (D : FinDigraph V) : Prop :=
  (∀ v : V, ∃! u : V, D.adj u v) ∧ IsWeaklyConnected D

/-- Ceiling of `ℓ / (q + 1)` as a natural number. -/
def ceilDiv (ℓ d : ℕ) : ℕ := (ℓ + d - 1) / d

/-- Penev–Stein–Trujillo-Negrete (arXiv:2608.00825), resolving Spiro's three questions on small
`q`-kernels in digraphs:
1. Theorem 1.2 (negative answer to Spiro Q2.3): for all `q ≥ 2` and `ℓ > q(q + 1)`, there is a
   strongly connected non-bipartite digraph of directed girth `ℓ` whose every `q`-kernel exceeds
   `max_{ℓ' ∈ L(D)} (⌈ℓ'/(q+1)⌉ / ℓ') |V(D)|`.
2. Theorem 1.3 (negative answer to Spiro Q7.7): for all `q, ℓ ≥ 2` and `ε > 0`, there is a
   strongly connected digraph of directed girth `ℓ` whose every `q`-kernel has density `> 1/q - ε`.
3. Theorem 1.6 (positive answer to Spiro Q7.7 for bipartite digraphs and odd `q ≥ 3`): every
   source-free bipartite digraph with an out-branching has a `q`-kernel of size `≤ |V|/(q+1) + 1`.
4. Theorem 1.7 (negative answer to Spiro Q2.3 for bipartite digraphs and even `q ≥ 2`): for every
   even `q ≥ 2` and `r ≥ 2`, there is a weakly connected source-free bipartite digraph on
   `n = r(5q+4)+1` vertices with `L(D) = {2(q+1)}` whose every `q`-kernel has size at least
   `n/(q+1) + (r-1)/(q+1)`.
5. Theorems 1.9 & 1.8 (positive answers to Spiro Q7.2 and Q2.3 for bipartite digraphs and odd
   `q ≥ 3`): both the unicyclic one-sided bound and the general source-free bipartite bound hold. -/
theorem main :
    (∀ q ℓ : ℕ, 2 ≤ q → q * (q + 1) < ℓ →
      ∃ (n : ℕ) (D : FinDigraph (Fin n)),
        0 < n ∧ IsStronglyConnected D ∧ ¬ IsBipartite D ∧ DirectedGirth D ℓ ∧
        ∀ Q : Finset (Fin n), IsQKernel D q Q →
          ∀ ℓ' : ℕ, HasDirCycle D ℓ' →
            ((ceilDiv ℓ' (q + 1) : ℚ) / (ℓ' : ℚ)) * (n : ℚ) < (Q.card : ℚ)) ∧
    (∀ q ℓ : ℕ, 2 ≤ q → 2 ≤ ℓ → ∀ ε : ℝ, 0 < ε →
      ∃ (n : ℕ) (D : FinDigraph (Fin n)),
        0 < n ∧ IsStronglyConnected D ∧ DirectedGirth D ℓ ∧
        ∀ Q : Finset (Fin n), IsQKernel D q Q →
          1 / (q : ℝ) - ε < (Q.card : ℝ) / (n : ℝ)) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (D : FinDigraph V) (q : ℕ),
      3 ≤ q → Odd q → IsSourceFree D → IsBipartite D → HasOutBranching D →
      ∃ Q : Finset V, IsQKernel D q Q ∧
        (Q.card : ℚ) ≤ (Fintype.card V : ℚ) / ((q + 1 : ℕ) : ℚ) + 1) ∧
    (∀ q r : ℕ, 2 ≤ q → Even q → 2 ≤ r →
      ∃ (n : ℕ) (D : FinDigraph (Fin n)),
        n = r * (5 * q + 4) + 1 ∧ IsWeaklyConnected D ∧ IsSourceFree D ∧ IsBipartite D ∧
        (∀ ℓ' : ℕ, HasDirCycle D ℓ' ↔ ℓ' = 2 * (q + 1)) ∧
        ∀ Q : Finset (Fin n), IsQKernel D q Q →
          ((ceilDiv (2 * (q + 1)) (q + 1) : ℚ) / ((2 * (q + 1) : ℕ) : ℚ)) * (n : ℚ) +
            ((r - 1 : ℕ) : ℚ) / ((q + 1 : ℕ) : ℚ) ≤ (Q.card : ℚ)) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (D : FinDigraph V) (c : V → Bool) (ℓ q : ℕ),
      3 ≤ q → Odd q → IsUnicyclic D → IsBipartition D c → HasDirCycle D ℓ →
      ∃ Q : Finset V, IsQKernel D q Q ∧ (∀ u ∈ Q, c u = false) ∧
        (Q.card : ℚ) ≤ 2 * ((ceilDiv ℓ (q + 1) : ℚ) / (ℓ : ℚ)) *
          ((Finset.univ.filter fun v => c v = false).card : ℚ)) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (D : FinDigraph V) (q : ℕ),
      Nonempty V → 3 ≤ q → Odd q → IsSourceFree D → IsBipartite D →
      ∃ (Q : Finset V) (ℓ : ℕ), IsQKernel D q Q ∧ HasDirCycle D ℓ ∧
        (Q.card : ℚ) ≤ ((ceilDiv ℓ (q + 1) : ℚ) / (ℓ : ℚ)) * (Fintype.card V : ℚ)) := by
  sorry

end OMA.S_arxiv_2608_00825
