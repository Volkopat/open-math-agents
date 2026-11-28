import Mathlib

/-!
# Eigenvalues of a special block matrix associated with a strongly connected graph

Source: https://mathoverflow.net/questions/107437
Credit: @koolkao

Question (Zhang Changhe, MathOverflow 107437, 2012; CC BY-SA 3.0). Let `G = (V, E, A)` be a
strongly connected directed graph, where `V = {1, 2, …, n}` denotes the vertex set, `E` is the
edge set, and `A` is the associated adjacency matrix with `0-1` weighting, that is `a_{i,j} = 1` if
`(j, i) ∈ E`, and `a_{i,j} = 0` otherwise. `B` and `D` are two diagonal matrices, where
`b_{ii} = ∑_{j=1}^n a_{i,j}` and `d_{ii} = ∑_{j=1}^n a_{j,i}`. In other words, the diagonal entries
of `B` are the row sums of `A`, and the diagonal entries of `D` are the column sums of `A`. Now
define a new matrix
`M = [[B - A, -A], [A - B, D]] ∈ ℝ^{2n × 2n}`.
Since the column sums of `M` are identically zero, zero must be one of its eigenvalues. Can I
claim that the rest eigenvalues all have positive real parts? […] Anyone can help prove or
disprove the above claim?

`main` states the claim; a disproof is a counterexample.

Translation choices:
* the vertex set is `Fin n`; the graph is given by its `0-1` adjacency matrix
  `A : Matrix (Fin n) (Fin n) ℝ` (every entry is `0` or `1`), with an edge from `j` to `i` exactly
  when `A i j = 1`, as in the source. Loops (`A i i = 1`) are not excluded, since the source does
  not exclude them;
* strongly connected: every vertex `v` is reachable from every vertex `u` along directed edges,
  that is `Relation.ReflTransGen (fun x y => A y x = 1) u v`;
* `M` is the block matrix `Matrix.fromBlocks (B - A) (-A) (A - B) D`, indexed by `Fin n ⊕ Fin n`;
* the eigenvalues of `M` are taken over `ℂ` with algebraic multiplicity: they are the roots of the
  characteristic polynomial of `M` viewed as a complex matrix (`Polynomial.roots`, a multiset of
  size `2n`). "The rest eigenvalues" are this multiset with one copy of the eigenvalue `0` removed
  (`Multiset.erase _ 0`), and the claim is that each of them has positive real part. (In
  particular the claim says that `0` is a simple eigenvalue.)
-/

namespace OMA.S_mo_107437

open Matrix

/-- The block matrix `M = [[B - A, -A], [A - B, D]]` of the source, where `B` (resp. `D`) is the
diagonal matrix of row (resp. column) sums of `A`. -/
noncomputable def blockM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  let B : Matrix (Fin n) (Fin n) ℝ := diagonal fun i => ∑ j, A i j
  let D : Matrix (Fin n) (Fin n) ℝ := diagonal fun i => ∑ j, A j i
  fromBlocks (B - A) (-A) (A - B) D

/-- For every strongly connected directed graph with `0-1` adjacency matrix `A`, the eigenvalues
of `M` other than one copy of `0` all have positive real part. -/
theorem main :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j, A i j = 0 ∨ A i j = 1) →
      (∀ u v : Fin n, Relation.ReflTransGen (fun x y => A y x = 1) u v) →
      ∀ z ∈ ((blockM A).map (algebraMap ℝ ℂ)).charpoly.roots.erase 0, 0 < z.re := by
  sorry

end OMA.S_mo_107437
