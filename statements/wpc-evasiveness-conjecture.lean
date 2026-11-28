import Mathlib

/-!
# Evasiveness (Aanderaa–Karp–Rosenberg) conjecture

Source: https://en.wikipedia.org/wiki/Aanderaa%E2%80%93Karp%E2%80%93Rosenberg_conjecture
Credit: @mgv27

Every nontrivial monotone property of n-vertex graphs is evasive: any deterministic algorithm
that queries whether pairs of vertices are adjacent must, in the worst case, query all
n(n−1)/2 pairs. Proved when n is a prime power (Kahn–Saks–Sturtevant); Rivest–Vuillemin
proved an Ω(n²) lower bound.

Formalization notes:
* A graph property on vertex set `Fin n` is `P : SimpleGraph (Fin n) → Prop`, required to be
  invariant under graph isomorphism, monotone increasing (closed under adding edges) and
  nontrivial (satisfied by some graph and failed by some graph).
* A deterministic adjacency-query algorithm is a binary decision tree whose internal nodes
  query a pair `s : Sym2 (Fin n)` (branching on `s ∈ G.edgeSet`) and whose leaves output a
  Boolean. Its worst-case number of queries is the tree depth.
* Evasive: every decision tree computing `P` has depth `≥ n(n−1)/2 = n.choose 2`.
-/

namespace OMA.S_wpc_evasiveness_conjecture

/-- Decision trees querying unordered vertex pairs of `Fin n`. -/
inductive DTree (n : ℕ) : Type
  | leaf : Bool → DTree n
  | node : Sym2 (Fin n) → DTree n → DTree n → DTree n

/-- Run a decision tree on a graph: at `node s l r` go to `r` if `s` is an edge, else `l`. -/
noncomputable def DTree.eval {n : ℕ} : DTree n → SimpleGraph (Fin n) → Bool
  | .leaf b, _ => b
  | .node s l r, G => by
      classical
      exact if s ∈ G.edgeSet then r.eval G else l.eval G

/-- Worst-case number of queries made by a decision tree. -/
def DTree.depth {n : ℕ} : DTree n → ℕ
  | .leaf _ => 0
  | .node _ l r => max l.depth r.depth + 1

/-- `P` is a nontrivial monotone graph property on `n` vertices. -/
def NontrivialMonotoneProperty (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : Prop :=
  (∀ G H : SimpleGraph (Fin n), Nonempty (G ≃g H) → (P G ↔ P H)) ∧
  (∀ G H : SimpleGraph (Fin n), G ≤ H → P G → P H) ∧
  (∃ G, P G) ∧ (∃ G, ¬ P G)

/-- The evasiveness conjecture. -/
theorem main : ∀ n : ℕ, ∀ P : SimpleGraph (Fin n) → Prop, NontrivialMonotoneProperty n P →
    ∀ t : DTree n, (∀ G, t.eval G = true ↔ P G) → n.choose 2 ≤ t.depth := by
  sorry

end OMA.S_wpc_evasiveness_conjecture
