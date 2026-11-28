import Mathlib

/-!
# The Bilu–Linial signing conjecture for Ramanujan graphs

Source: https://arxiv.org/abs/2609.15591 ("A 3-regular counterexample to the Bilu–Linial signing
conjecture", 2026)
Credit: Sudharsan Rajendiran

The Bilu–Linial signing conjecture asserts that every `d`-regular graph has a signing of its
edges whose signed adjacency matrix has all its eigenvalues in `[-2√(d - 1), 2√(d - 1)]`. The paper
constructs a finite connected simple cubic graph `F` for which every signing has an eigenvalue
outside `[-2√2, 2√2]`, disproving the conjecture for general regular graphs. The graph `F` is not
Ramanujan, and the conjecture restricted to Ramanujan base graphs remains open. We state that open
problem: every `d`-regular Ramanujan graph has such a signing. A disproof is the negation of
`main`.

Conventions:
- Graphs are `SimpleGraph V` on a finite vertex type; `d`-regular means every vertex has degree
  `d`. We take `d ≥ 2`: for `d = 1` (a perfect matching) every signed adjacency matrix has
  eigenvalues `±1`, so the bound `2√0 = 0` fails trivially, and the conjecture is not meant there.
- Ramanujan: `G` is connected and every real eigenvalue `λ` of its adjacency matrix with
  `|λ| ≠ d` satisfies `|λ| ≤ 2√(d - 1)` (the standard definition; `±d` are the trivial
  eigenvalues). Adjacency and signed adjacency matrices are real symmetric, so all their
  eigenvalues are real.
- A signing assigns `+1` or `-1` to every edge. It is given by `σ : V → V → ℝ`, symmetric, with
  `σ u v ∈ {1, -1}` whenever `u` and `v` are adjacent (its other values are irrelevant). The
  signed adjacency matrix has entry `σ u v` at adjacent `u, v` and `0` elsewhere.
- Eigenvalues are those of the matrix acting on `V → ℝ` (`Matrix.toLin'`).
-/

namespace OMA.S_arxiv_2609_15591

/-- The signed adjacency matrix of `G` for the signing `σ`. -/
noncomputable def signedAdj {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (σ : V → V → ℝ) : Matrix V V ℝ :=
  Matrix.of fun u v => if G.Adj u v then σ u v else 0

/-- `σ` is a signing of the edges of `G`. -/
def IsSigning {V : Type} (G : SimpleGraph V) (σ : V → V → ℝ) : Prop :=
  (∀ u v, σ u v = σ v u) ∧ ∀ u v, G.Adj u v → (σ u v = 1 ∨ σ u v = -1)

/-- `G` is a `d`-regular Ramanujan graph. -/
def IsRamanujan {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) : Prop :=
  G.Connected ∧ G.IsRegularOfDegree d ∧
    ∀ ν : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℝ)) ν → |ν| ≠ d →
      |ν| ≤ 2 * Real.sqrt ((d : ℝ) - 1)

/-- The Bilu–Linial signing conjecture for Ramanujan base graphs: every `d`-regular Ramanujan
graph with `d ≥ 2` has a signing whose signed adjacency matrix has all its eigenvalues in
`[-2√(d - 1), 2√(d - 1)]`. -/
theorem main : ∀ (d : ℕ), 2 ≤ d → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], IsRamanujan G d →
    ∃ σ : V → V → ℝ, IsSigning G σ ∧
      ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (signedAdj G σ)) μ →
        |μ| ≤ 2 * Real.sqrt ((d : ℝ) - 1) := by
  sorry

end OMA.S_arxiv_2609_15591
