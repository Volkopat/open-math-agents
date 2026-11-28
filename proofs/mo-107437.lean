import OMAStatements.S_mo_107437
import Mathlib

/-!
MathOverflow 107437: the claim fails for the directed 4-cycle `0 → 1 → 2 → 3 → 0`. There `B = D = I`
and `M` has the eigenvalue `i` (real part `0`), with eigenvector `(x, i x)`, `x = (1, i, -1, -i)`.
-/

open Matrix OMA.S_mo_107437

namespace OMA.P107437

/-- The directed 4-cycle `0 → 1 → 2 → 3 → 0`: `A i j = 1` iff `j + 1 = i`. -/
noncomputable def cyc : Matrix (Fin 4) (Fin 4) ℝ := fun i j => if j + 1 = i then 1 else 0

lemma cyc01 (i j : Fin 4) : cyc i j = 0 ∨ cyc i j = 1 := by
  unfold cyc; split_ifs <;> simp

lemma cyc_step (x : Fin 4) : cyc (x + 1) x = 1 := by
  simp [cyc]

lemma cyc_strong (u v : Fin 4) : Relation.ReflTransGen (fun x y => cyc y x = 1) u v := by
  have key : ∀ u v : Fin 4, v = u ∨ v = u + 1 ∨ v = u + 1 + 1 ∨ v = u + 1 + 1 + 1 := by decide
  rcases key u v with rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (cyc_step u)
  · exact Relation.ReflTransGen.tail (b := u + 1) (c := u + 1 + 1)
      (Relation.ReflTransGen.single (cyc_step u)) (cyc_step (u + 1))
  · exact Relation.ReflTransGen.tail (b := u + 1 + 1) (c := u + 1 + 1 + 1)
      (Relation.ReflTransGen.tail (b := u + 1) (c := u + 1 + 1)
        (Relation.ReflTransGen.single (cyc_step u)) (cyc_step (u + 1))) (cyc_step (u + 1 + 1))

lemma rowsum (i : Fin 4) : ∑ j, cyc i j = 1 := by
  fin_cases i <;> simp [cyc] <;> decide

lemma colsum (i : Fin 4) : ∑ j, cyc j i = 1 := by
  fin_cases i <;> simp [cyc]

lemma blockM_cyc : blockM cyc = fromBlocks (1 - cyc) (-cyc) (cyc - 1) 1 := by
  have hB : (diagonal fun i => ∑ j, cyc i j) = 1 := by
    rw [← diagonal_one]; congr 1; funext i; exact rowsum i
  have hD : (diagonal fun i => ∑ j, cyc j i) = 1 := by
    rw [← diagonal_one]; congr 1; funext i; exact colsum i
  simp only [blockM, hB, hD]

/-- An eigenvector of `M` for the eigenvalue `i`. -/
noncomputable def vec : Fin 4 ⊕ Fin 4 → ℂ
  | Sum.inl k => Complex.I ^ (k : ℕ)
  | Sum.inr k => Complex.I ^ ((k : ℕ) + 1)

lemma vec_ne : vec ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl 0)
  simp [vec] at this

lemma eigen :
    (scalar (Fin 4 ⊕ Fin 4) Complex.I - (blockM cyc).map (algebraMap ℝ ℂ)) *ᵥ vec = 0 := by
  rw [blockM_cyc]
  funext r
  rcases r with k | k <;> fin_cases k <;>
    simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four, cyc, vec,
      fromBlocks, Matrix.one_apply, Matrix.sub_apply, Matrix.neg_apply, pow_succ,
      Complex.ext_iff]

lemma I_mem : Complex.I ∈ ((blockM cyc).map (algebraMap ℝ ℂ)).charpoly.roots.erase 0 := by
  rw [Multiset.mem_erase_of_ne Complex.I_ne_zero,
    Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero, Polynomial.IsRoot,
    Matrix.eval_charpoly]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨vec, vec_ne, eigen⟩

end OMA.P107437

open OMA.P107437 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_107437.main) := by
  intro h
  have := h 4 cyc cyc01 cyc_strong Complex.I I_mem
  simp at this
