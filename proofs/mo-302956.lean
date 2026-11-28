import OMAStatements.S_mo_302956
import Mathlib

/-!
# MathOverflow 302956: symmetric-function inequalities do not force majorisation

Witness with `n = 3`: `x = (5, 5, 0)` and `y = (6, 2, 2)`.

* Both are non-negative, non-increasing and sum to `10`.
* `e₂(x) = 25 ≤ 28 = e₂(y)`, `e₃(x) = 0 ≤ 24 = e₃(y)`,
  `p₂(y) = 44 ≤ 50 = p₂(x)`, `p₃(y) = 232 ≤ 250 = p₃(x)`.
* `x` does not majorise `y`: already the first partial sums give `y₀ = 6 > 5 = x₀`.
-/

namespace OMA.S_mo_302956

lemma esymm_two (x : Fin 3 → ℝ) : esymm 2 x = x 0 * x 1 + x 0 * x 2 + x 1 * x 2 := by
  unfold esymm
  rw [show (Finset.univ : Finset (Fin 3)).powersetCard 2 = {{0, 1}, {0, 2}, {1, 2}} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.prod_pair (by decide), Finset.prod_pair (by decide), Finset.prod_pair (by decide)]
  ring

lemma esymm_three (x : Fin 3 → ℝ) : esymm 3 x = x 0 * x 1 * x 2 := by
  unfold esymm
  rw [show (Finset.univ : Finset (Fin 3)).powersetCard 3 = {{0, 1, 2}} from by decide,
    Finset.sum_singleton, Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
  ring

lemma psum_three (k : ℕ) (x : Fin 3 → ℝ) : psum k x = x 0 ^ k + x 1 ^ k + x 2 ^ k := by
  unfold psum
  rw [Fin.sum_univ_three]

end OMA.S_mo_302956

open OMA.S_mo_302956 in
theorem OMA.solution : type_of% @OMA.S_mo_302956.main := by
  have x2 : (![5, 5, 0] : Fin 3 → ℝ) 2 = 0 := rfl
  have y2 : (![6, 2, 2] : Fin 3 → ℝ) 2 = 2 := rfl
  refine ⟨3, ![5, 5, 0], ![6, 2, 2], by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · rw [Fin.sum_univ_three, Fin.sum_univ_three]
    show (5 : ℝ) + 5 + 0 = 6 + 2 + 2
    norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hij; decide) | norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hij; decide) | norm_num
  · intro k hk2 hk3
    interval_cases k
    · rw [esymm_two, esymm_two, psum_three, psum_three]
      norm_num [x2, y2]
    · rw [esymm_three, esymm_three, psum_three, psum_three]
      norm_num [x2, y2]
  · rintro ⟨-, -, -, h⟩
    have h1 := h 1 le_rfl (by norm_num)
    rw [show (Finset.univ.filter (fun i : Fin 3 => i.val < 1)) = {0} from by decide,
      Finset.sum_singleton, Finset.sum_singleton] at h1
    norm_num at h1
