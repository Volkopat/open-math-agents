import OMAStatements.S_mo_256897
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Matrix-optimal factors need not be tensor-optimal

An explicit counterexample to Ulderique Demoitre's question:
https://mathoverflow.net/questions/256897

The input columns are the first two standard basis vectors in ℝ³.
The single column −e₀ minimizes the order-two Frobenius distance.
At order three, replacing it by +e₀ lowers the squared distance from 5 to 1.

Formal statement credit: @etaubman.
The recursive finite-function sum identity and tuple evaluation follow the earlier companion
a1e42e582e28f357b0e7309df8d44d8a14120ff7 by @etaubman.
The standard-basis and singleton linear-independence APIs replace manual coordinate cases.
Disproof credit: @grp06, merged PR #30027
(ad19020a95ccdf972e051c28fa0224b08f47aa81).
-/

open scoped BigOperators
open OMA.S_mo_256897

namespace OMA.Mo256897Counterexample

private def input : Matrix (Fin 3) (Fin 2) ℝ :=
  fun i j => if i.val = j.val then 1 else 0

private def firstColumn (t : ℝ) : Matrix (Fin 3) (Fin 1) ℝ :=
  fun i _ => if i.val = 0 then t else 0

private theorem input_rank : FullColumnRank input := by
  unfold FullColumnRank
  convert (Pi.basisFun ℝ (Fin 3)).linearIndependent.comp
    (Fin.castLE (show 2 ≤ 3 from by decide) : Fin 2 → Fin 3) (Fin.castLE_injective _) using 1
  ext j i
  simp [input, Pi.basisFun_apply, Pi.single_apply, Fin.ext_iff, eq_comm]

private theorem firstColumn_rank {t : ℝ} (ht : t ≠ 0) :
    FullColumnRank (firstColumn t) := by
  rw [FullColumnRank, linearIndependent_unique_iff]
  intro h
  exact ht (by simpa [firstColumn] using congrFun h 0)

private theorem sum_coordinates (h : ℕ) (f : (Fin (h + 1) → Fin 3) → ℝ) :
    (∑ a, f a) = ∑ i, ∑ a, f (Fin.cons i a) := by
  calc
    _ = ∑ p : Fin 3 × (Fin h → Fin 3), f (Fin.cons p.1 p.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (h + 1) => Fin 3))
        _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _


private theorem squared_error_two (N : Matrix (Fin 3) (Fin 1) ℝ) :
    squaredError input N 2 =
      1 + (N 0 0 ^ 2 + N 1 0 ^ 2 + N 2 0 ^ 2 - 1) ^ 2 + 2 * N 2 0 ^ 2 := by
  simp [squaredError, tensor, sum_coordinates, Fin.sum_univ_three,
    Fin.sum_univ_two, Fin.prod_univ_succ, input]
  ring

private theorem cons_two (x : Fin 3) (a : Fin 2 → Fin 3) :
    @Fin.cons 2 (fun _ => Fin 3) x a (2 : Fin 3) = a 1 := rfl

private theorem squared_error_three_formula (t : ℝ) :
    squaredError input (firstColumn t) 3 = (1 - t * t * t) ^ 2 + 1 := by
  norm_num [squaredError, tensor, sum_coordinates, Fin.sum_univ_three,
    Fin.sum_univ_two, Fin.prod_univ_succ, input, firstColumn, cons_two, show (2 : Fin 3) ≠ 0 by decide]
  ring

private theorem neg_minimizes_two : Minimizes input (firstColumn (-1)) 2 := by
  intro N _
  unfold error
  apply Real.sqrt_le_sqrt
  rw [squared_error_two, squared_error_two]
  norm_num [firstColumn]
  nlinarith [sq_nonneg (N 0 0 ^ 2 + N 1 0 ^ 2 + N 2 0 ^ 2 - 1), sq_nonneg (N 2 0)]


theorem disprove : ¬ claim := by
  intro h
  have hmin :=
    h 3 2 1 (by decide) (by decide) input (firstColumn (-1))
      input_rank (firstColumn_rank (by norm_num)) neg_minimizes_two 3 (by decide)
      (firstColumn 1) (firstColumn_rank (by norm_num))
  unfold error at hmin
  have hneg : squaredError input (firstColumn (-1)) 3 = 5 := by
    rw [squared_error_three_formula]
    norm_num
  have hpos : squaredError input (firstColumn 1) 3 = 1 := by
    rw [squared_error_three_formula]
    norm_num
  rw [hneg, hpos] at hmin
  exact (not_le_of_gt (Real.sqrt_lt_sqrt (by norm_num) (show (1 : ℝ) < 5 by norm_num))) hmin

end OMA.Mo256897Counterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_256897.main) :=
  OMA.Mo256897Counterexample.disprove
