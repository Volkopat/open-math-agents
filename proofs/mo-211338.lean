import OMAStatements.S_mo_211338

-- Problem: Searching a specific matrix whose determinant is a product which is similar to the Vandermonde determinant
-- Upstream: statements/mo-211338.lean (declaration OMA.S_mo_211338.main)
-- Credit: @FrancoisCharroin
-- Proof via Polynomial.resultant_prod_left and Polynomial.resultant_X_sub_C_left.

namespace OMA.Mo211338

open Polynomial OMA.S_mo_211338

lemma natDegree_node {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (x : Fin n → R)
    (S : Finset (Fin n)) : (node x S).natDegree = S.card := by
  unfold node
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (x i))]
  simp

lemma det_crossMatrix {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (x : Fin n → R)
    (A B : Finset (Fin n)) :
    (crossMatrix x A B).det = ∏ i ∈ A, ∏ j ∈ B, (x j - x i) := by
  have hdegB : (node x B).natDegree = B.card := natDegree_node x B
  have hdegA : (node x A).natDegree ≤ A.card := (natDegree_node x A).le
  have hlc : ∏ j ∈ B, (X - C (x j)).leadingCoeff ≠ 0 := by
    simp [Polynomial.leadingCoeff_X_sub_C]
  have hres :
      (crossMatrix x A B).det = (node x B).resultant (node x A) B.card A.card := rfl
  rw [hres, ← hdegB]
  change (∏ j ∈ B, (X - C (x j))).resultant (node x A)
      (∏ j ∈ B, (X - C (x j))).natDegree A.card = _
  rw [Polynomial.resultant_prod_left B (fun j => X - C (x j)) (node x A) A.card hlc hdegA]
  have hterm :
      ∀ j ∈ B,
        (X - C (x j)).resultant (node x A) (X - C (x j)).natDegree A.card =
          ∏ i ∈ A, (x j - x i) := by
    intro j _
    rw [Polynomial.natDegree_X_sub_C, Polynomial.resultant_X_sub_C_left _ _ (x j) hdegA]
    simp [node, Polynomial.eval_prod]
  rw [Finset.prod_congr rfl hterm, Finset.prod_comm]

end OMA.Mo211338

theorem OMA.solution : type_of% @OMA.S_mo_211338.main := by
  intro R _ _ n x A B _ _ _
  have hdet := OMA.Mo211338.det_crossMatrix x A B
  refine ⟨hdet, ?_⟩
  rw [hdet]
  simp only [Finset.prod_ne_zero_iff, sub_ne_zero]
  exact ⟨fun h i hi j hj => (h i hi j hj).symm, fun h i hi j hj => (h i hi j hj).symm⟩
