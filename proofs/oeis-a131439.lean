import OMAStatements.S_oeis_a131439
import Mathlib

open OMA.S_oeis_a131439
open fwdDiff

namespace P131439

theorem seq_eq (n : ℕ) : OMA.S_oeis_a131439.sequence n = (fwdDiff 1)^[n] input 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  unfold OMA.S_oeis_a131439.sequence
  apply Finset.sum_congr rfl
  intro k _
  simp only [zsmul_eq_mul, smul_eq_mul, zero_add, Nat.smul_one_eq_cast, Nat.cast_id]
  push_cast
  ring

theorem it2 : (fwdDiff 1)^[2] input = fun k : ℕ => ((k : ℤ) + 7) * 2 ^ (k + 1) := by
  funext k
  show (fwdDiff 1 (fwdDiff 1 input)) k = _
  simp only [fwdDiff, input]
  push_cast
  ring

theorem itm (m : ℕ) : (fwdDiff 1)^[m + 2] input = fun k : ℕ => ((k : ℤ) + 7 + 2 * m) * 2 ^ (k + 1) := by
  induction m with
  | zero => rw [it2]; funext k; simp
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, Function.iterate_succ_apply', ih]
    funext k
    simp only [fwdDiff]
    push_cast
    ring

end P131439

theorem OMA.solution : type_of% @OMA.S_oeis_a131439.main := by
  refine ⟨by decide, by decide, fun k => ?_⟩
  rw [P131439.seq_eq, P131439.itm]
  simp
  ring
