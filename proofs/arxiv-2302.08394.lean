import OMAStatements.S_arxiv_2302_08394

/-!
The two nine-vertex trees in Burghart's Remark 16
(https://arxiv.org/abs/2302.08394) have the same list of monomials,
including multiplicities. They differ in whether a vertex at distance two
from the root has degree three.
-/

namespace OMA.BurghartTreeWitness

open Finset MvPolynomial OMA.S_arxiv_2302_08394

private abbrev V := Fin 9

private def tree1 : RootedTree 8 where
  parent := ![0, 0, 1, 2, 3, 2, 0, 6, 6]
  parent_lt := by decide

private def tree2 : RootedTree 8 where
  parent := ![0, 0, 1, 2, 3, 3, 1, 0, 7]
  parent_lt := by decide

private def subsets1 : List (Finset V) :=
  [∅, {0}, {0, 1}, {0, 6}, {0, 1, 2}, {0, 1, 6}, {0, 1, 2, 3},
    {0, 1, 2, 6}, {0, 1, 2, 3, 6}]

private def subsets2 : List (Finset V) :=
  [∅, {0}, {0, 7}, {0, 1}, {0, 1, 2}, {0, 1, 7}, {0, 1, 2, 7},
    {0, 1, 2, 3}, {0, 1, 2, 3, 7}]

private def exponents (T : RootedTree 8) (l : List (Finset V)) : List (ℕ × ℕ) :=
  l.map fun s => (s.card, T.boundaryCard s)

private noncomputable def term (ij : ℕ × ℕ) : MvPolynomial (Fin 2) ℤ :=
  X 0 ^ ij.1 * X 1 ^ ij.2

private theorem poly_list (T : RootedTree 8) (l : List (Finset V))
    (hsubsets : univ.filter T.IsAdmissible = l.toFinset) (hl : l.Nodup) :
    T.A = ((exponents T l).map term).sum := by
  rw [RootedTree.A, hsubsets, List.sum_toFinset _ hl, exponents, List.map_map]
  rfl

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 3000 in
private theorem admissibles1 : univ.filter tree1.IsAdmissible = subsets1.toFinset := by decide

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 3000 in
private theorem admissibles2 : univ.filter tree2.IsAdmissible = subsets2.toFinset := by decide

private theorem same_poly : tree1.A = tree2.A := by
  have hterms : exponents tree1 subsets1 = exponents tree2 subsets2 := by decide
  rw [poly_list tree1 subsets1 admissibles1 (by decide),
    poly_list tree2 subsets2 admissibles2 (by decide), hterms]

private def degree (T : RootedTree 8) (v : V) : ℕ :=
  (univ.filter (T.Adj v)).card

private theorem preserve_degree {T₁ T₂ : RootedTree 8} {σ : Equiv.Perm V}
    (hσ : ∀ v w, T₁.Adj v w ↔ T₂.Adj (σ v) (σ w)) (v : V) :
    degree T₁ v = degree T₂ (σ v) := by
  have hset : (univ.filter (T₁.Adj v)).map σ.toEmbedding = univ.filter (T₂.Adj (σ v)) := by
    ext w
    simp only [mem_map, mem_filter, mem_univ, true_and, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hσ v u).mp hu
    · intro hw
      refine ⟨σ.symm w, (hσ v (σ.symm w)).mpr ?_, σ.apply_symm_apply w⟩
      rwa [σ.apply_symm_apply]
  rw [degree, degree, ← hset, card_map]

private theorem noniso : ¬ tree1.Isomorphic tree2 := by
  rintro ⟨σ, h0, hσ⟩
  have hbad : ∀ a b : V, tree2.Adj 0 a → tree2.Adj a b → b ≠ 0 → degree tree2 b ≠ 3 := by
    decide
  apply hbad (σ 1) (σ 2)
  · exact h0 ▸ (hσ 0 1).mp (by decide)
  · exact (hσ 1 2).mp (by decide)
  · rw [← h0]
    exact fun h => (by decide : (2 : V) ≠ 0) (σ.injective h)
  · rw [← preserve_degree hσ]
    decide

end OMA.BurghartTreeWitness

open OMA.BurghartTreeWitness in
theorem OMA.solution : type_of% @OMA.S_arxiv_2302_08394.main :=
  ⟨8, tree1, tree2, noniso, same_poly⟩
