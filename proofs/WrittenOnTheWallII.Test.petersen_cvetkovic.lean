import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph Matrix Polynomial WrittenOnTheWallII.Test

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.petersen_cvetkovic := by
  let A := PetersenGraph.adjMatrix ℚ
  let B : Matrix PetersenVertex (Fin 5) ℚ := of fun v i => if i ∈ v.1 then 1 else 0
  let J : Matrix (Fin 5) (Fin 5) ℚ := vecMulVec 1 1
  let D := (1/4 : ℚ) • J - 1
  have h₁ : A - 1 = (B*D) * Bᵀ := by decide +kernel
  have h₂ : Bᵀ * (B*D) = J - scalar _ 3 := by decide +kernel
  have hc : Fintype.card (Fin 5) ≤ Fintype.card PetersenVertex := by decide +kernel
  have hcard : Fintype.card PetersenVertex = 10 := by decide +kernel
  have hs : A = A - 1 - scalar _ (-1) := by rw [map_neg, map_one, sub_neg_eq_add, sub_add_cancel]
  have hp : A.charpoly = (X - 1)^5 * (X + 2)^4 * (X - 3) := by
    rw [hs, charpoly_sub_scalar, h₁, charpoly_mul_comm_of_le _ _ hc, h₂,
      charpoly_sub_scalar, charpoly_vecMulVec, hcard]
    norm_num [dotProduct, Fin.sum_univ_succ, Polynomial.smul_eq_C_mul, Polynomial.C_ofNat]
    ring
  let s : Multiset ℝ := 3 ::ₘ 1 ::ₘ 1 ::ₘ 1 ::ₘ 1 ::ₘ 1 ::ₘ -2 ::ₘ -2 ::ₘ -2 ::ₘ -2 ::ₘ 0
  have hm : PetersenGraph.adjMatrix ℝ = A.map (Rat.castHom ℝ) := by
    ext i j
    change (if PetersenGraph.Adj i j then (1 : ℝ) else 0) =
      (Rat.castHom ℝ) (if PetersenGraph.Adj i j then 1 else 0)
    split <;> norm_num
  have hr : (PetersenGraph.adjMatrix ℝ).charpoly = (s.map fun a => X-C a).prod := by
    rw [hm, Matrix.charpoly_map, hp]
    simp [s, Multiset.map_cons, Multiset.prod_cons, Polynomial.C_ofNat]
    ring
  unfold cvetkovic
  rw [hr, roots_multiset_prod_X_sub_C]
  simp only [s, Multiset.countP_cons, Multiset.countP_zero]
  norm_num
