import OMAStatements.S_mo_237999
import Mathlib

/-!
MathOverflow 237999: `A = [[1, -1], [0, 0]]` has zero row sums and is weakly diagonally dominant;
it admits no decoupling (any `R D Rᵀ` with `D` diagonal is symmetric), and `xᵀ A x = -1` at
`x = (1, 2)`.
-/

namespace OMA.P237999

open Matrix

def A : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 0, 0]

lemma rows : ∀ i, ∑ j, A i j = 0 := by
  intro i; fin_cases i <;> simp [A, Fin.sum_univ_two]

lemma dom : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ |A i i| := by
  intro i
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  fin_cases i <;> norm_num [A, Fin.sum_univ_two]

lemma split2 : ∀ S : Finset (Fin 2), S.Nonempty → S ≠ Finset.univ →
    (((0 : Fin 2) ∈ S ↔ (1 : Fin 2) ∉ S) ∧ ((1 : Fin 2) ∈ S ↔ (0 : Fin 2) ∉ S)) := by
  decide

lemma nodec : ¬ ∃ (R D : Matrix (Fin 2) (Fin 2) ℝ) (S : Finset (Fin 2)), IsUnit R ∧
    S.Nonempty ∧ S ≠ Finset.univ ∧ (∀ i j, (i ∈ S ↔ j ∉ S) → D i j = 0) ∧ A = R * D * Rᵀ := by
  rintro ⟨R, D, S, -, hS1, hS2, hD, hA⟩
  obtain ⟨h01, h10⟩ := split2 S hS1 hS2
  have hDt : Dᵀ = D := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD 0 1 h01, hD 1 0 h10]
  have hAt : Aᵀ = A := by
    rw [hA, transpose_mul, transpose_mul, transpose_transpose, hDt, Matrix.mul_assoc]
  have := congrFun (congrFun hAt 0) 1
  simp [A] at this

lemma neg : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ (A *ᵥ ![1, 2]) < 0 := by
  norm_num [A, dotProduct, mulVec, Fin.sum_univ_two]

theorem disproof_aux :
    ¬ ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ),
      (∀ i, ∑ j, A i j = 0) →
      (∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ |A i i|) →
      (¬ ∃ (R D : Matrix (Fin d) (Fin d) ℝ) (S : Finset (Fin d)), IsUnit R ∧ S.Nonempty ∧
          S ≠ Finset.univ ∧ (∀ i j, (i ∈ S ↔ j ∉ S) → D i j = 0) ∧ A = R * D * Rᵀ) →
      ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  intro h
  exact absurd (h 2 A rows dom nodec ![1, 2]) (not_le.2 neg)

end OMA.P237999

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_237999.main) := OMA.P237999.disproof_aux
