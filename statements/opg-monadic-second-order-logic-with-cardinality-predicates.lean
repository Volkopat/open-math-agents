import Mathlib

/-!
# Monadic second-order logic with cardinality predicates

Source: https://www.openproblemgarden.org/op/monadic_second_order_logic_with_cardinality_predicates
Credit: @eltociear

Source text (Courcelle; Open Problem Garden, posted by dberwanger, 2012):
"The problem concerns the extension of Monadic Second Order Logic (over a binary relation
representing the edge relation) with the following atomic formulas:
  * Card(X) = Card(Y)
  * Card(X) belongs to A
where A is a fixed recursive set of integers. Let us fix k and a closed formula F in this
language. Conjecture: Is it true that the validity of F for a graph G of tree-width at most k
can be tested in polynomial time in the size of G?"

Formalization choices (standard readings, stated here for the reviewer):
* Graph = a finite structure with vertex set `Fin n` and one binary edge relation `E`
  (the source's "binary relation representing the edge relation"; no symmetry or
  irreflexivity is imposed). Its tree-width is the tree-width of its underlying undirected
  (Gaifman) graph: every pair `u v` with `E u v` must lie in a common bag.
* MSO has first-order (vertex) variables and monadic (vertex-set) variables, atoms
  `edg(x,y)`, `x = y`, `x ∈ X`, plus the two cardinality atoms of the source, and is closed
  under `¬`, `∧`, `∃x`, `∃X` (the other connectives and `∀` are definable). "Closed" = no free
  variables of either sort.
* `A ⊆ ℕ` with `ComputablePred (· ∈ A)` ("fixed recursive set of integers"; cardinalities
  are natural numbers, so only `A ∩ ℕ` matters).
* "Polynomial time in the size of G" uses Mathlib's `Turing.TM2ComputableInPolyTime`, with
  `G` written as `n` in unary, a separator, then the `n²` adjacency bits (length `n² + n + 1`,
  polynomial in the size of `G`). The machine may depend on `A`, `k` and `F` (they are fixed
  first), and it only has to be correct on graphs of tree-width at most `k`.
* The question "Is it true that ...?" is stated as the positive claim; a disproof is its
  negation.
-/

namespace OMA.S_opg_monadic_second_order_logic_with_cardinality_predicates

/-- A finite graph: vertex set `Fin n`, one binary edge relation. -/
structure Graph where
  n : ℕ
  E : Fin n → Fin n → Bool

/-- The edge relation, read on natural-number vertex names (false outside `[0, n)`). -/
def Graph.adj (G : Graph) (i j : ℕ) : Prop :=
  ∃ (hi : i < G.n) (hj : j < G.n), G.E ⟨i, hi⟩ ⟨j, hj⟩ = true

/-- Binary encoding of a graph: `n` in unary, `false`, then the adjacency matrix row by row. -/
def Graph.encode (G : Graph) : List Bool :=
  List.replicate G.n true ++
    false :: (List.finRange G.n).flatMap (fun i => (List.finRange G.n).map (G.E i))

/-- `G` has tree-width at most `k`: a tree decomposition of its underlying undirected graph
with every bag of size at most `k + 1`. -/
def Graph.TreewidthLE (G : Graph) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (bag : Fin m → Finset (Fin G.n)),
    T.IsTree ∧
    (∀ v, ∃ t, v ∈ bag t) ∧
    (∀ u v, G.E u v = true → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
    (∀ v, (T.induce {t | v ∈ bag t}).Connected) ∧
    (∀ t, (bag t).card ≤ k + 1)

/-- Formulas of MSO over one binary relation, with the two cardinality atoms.
Vertex variables and set variables are both indexed by `ℕ`, in separate namespaces. -/
inductive Formula where
  | edge (x y : ℕ)
  | eq (x y : ℕ)
  | mem (x X : ℕ)
  | cardEq (X Y : ℕ)
  | cardIn (X : ℕ)
  | neg (φ : Formula)
  | and (φ ψ : Formula)
  | exV (x : ℕ) (φ : Formula)
  | exS (X : ℕ) (φ : Formula)

/-- Free vertex variables. -/
def Formula.freeV : Formula → Finset ℕ
  | .edge x y => {x, y}
  | .eq x y => {x, y}
  | .mem x _ => {x}
  | .cardEq _ _ => ∅
  | .cardIn _ => ∅
  | .neg φ => φ.freeV
  | .and φ ψ => φ.freeV ∪ ψ.freeV
  | .exV x φ => φ.freeV.erase x
  | .exS _ φ => φ.freeV

/-- Free set variables. -/
def Formula.freeS : Formula → Finset ℕ
  | .edge _ _ => ∅
  | .eq _ _ => ∅
  | .mem _ X => {X}
  | .cardEq X Y => {X, Y}
  | .cardIn X => {X}
  | .neg φ => φ.freeS
  | .and φ ψ => φ.freeS ∪ ψ.freeS
  | .exV _ φ => φ.freeS
  | .exS X φ => φ.freeS.erase X

/-- A closed formula (sentence). -/
def Formula.Closed (φ : Formula) : Prop := φ.freeV = ∅ ∧ φ.freeS = ∅

/-- Satisfaction in `G`, with `A` interpreting `Card(X) ∈ A`. Vertex variables take values in
`[0, G.n)` and set variables take subsets of it once bound by a quantifier. -/
def Formula.Sat (A : Set ℕ) (G : Graph) : Formula → (ℕ → ℕ) → (ℕ → Finset ℕ) → Prop
  | .edge x y, ρ, _ => G.adj (ρ x) (ρ y)
  | .eq x y, ρ, _ => ρ x = ρ y
  | .mem x X, ρ, σ => ρ x ∈ σ X
  | .cardEq X Y, _, σ => (σ X).card = (σ Y).card
  | .cardIn X, _, σ => (σ X).card ∈ A
  | .neg φ, ρ, σ => ¬ φ.Sat A G ρ σ
  | .and φ ψ, ρ, σ => φ.Sat A G ρ σ ∧ ψ.Sat A G ρ σ
  | .exV x φ, ρ, σ => ∃ v < G.n, φ.Sat A G (Function.update ρ x v) σ
  | .exS X φ, ρ, σ => ∃ S ⊆ Finset.range G.n, φ.Sat A G ρ (Function.update σ X S)

/-- Truth of a sentence in `G` (the initial valuation is irrelevant for closed formulas). -/
def Models (A : Set ℕ) (G : Graph) (F : Formula) : Prop :=
  F.Sat A G (fun _ => 0) (fun _ => ∅)

/-- Courcelle's question, positive form: for every fixed recursive `A`, every fixed `k` and
every fixed closed formula `F`, some polynomial-time Turing machine decides `G ⊨ F` on all
graphs `G` of tree-width at most `k`. -/
theorem main :
    ∀ (A : Set ℕ), ComputablePred (· ∈ A) →
    ∀ (k : ℕ) (F : Formula), F.Closed →
    ∃ f : Graph → Bool,
      Nonempty (Turing.TM2ComputableInPolyTime Graph.encode (fun b : Bool => [b]) f) ∧
      ∀ G : Graph, G.TreewidthLE k → (f G = true ↔ Models A G F) := by
  sorry

end OMA.S_opg_monadic_second_order_logic_with_cardinality_predicates
