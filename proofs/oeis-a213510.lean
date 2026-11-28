import OMAStatements.S_oeis_a213510
import Mathlib

/-!
# OEIS A213510: Irvine's conjecture (partial sums of A064099)

The inclusive depth of node `i` of the complete ternary tree (root `0`, children of `j` are
`3j+1, 3j+2, 3j+3`) is exactly `⌈log₃(2i + 3)⌉`, so the two sums agree term by term.

Induction: node `i+1` has parent `q = ⌊i/3⌋`. If `c = ⌈log₃(2q + 3)⌉`, then
`3^(c-1) < 2q + 3 ≤ 3^c`; as `3^(c-1)` is odd, in fact `3^(c-1) ≤ 2q + 1`, so
`3^c ≤ 6q + 3 < 2(i+1) + 3 ≤ 6q + 9 ≤ 3^(c+1)`, i.e. `⌈log₃(2(i+1) + 3)⌉ = c + 1`.
-/

namespace OMA.A213510Aux

open OMA.S_oeis_a213510

theorem depth_eq (i : ℕ) : inclusiveDepth i = Nat.clog 3 (3 + 2 * i) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases i with _ | i
    · rw [inclusiveDepth, show 3 + 2 * 0 = 3 ^ 1 by norm_num, Nat.clog_pow 3 1 (by norm_num)]
    · rw [inclusiveDepth, ih (i / 3) (by omega)]
      set c := Nat.clog 3 (3 + 2 * (i / 3)) with hc
      have hcpos : 0 < c := Nat.clog_pos (by norm_num) (by omega)
      have hup : 3 + 2 * (i / 3) ≤ 3 ^ c := Nat.le_pow_clog (by norm_num) _
      have hlow : 3 ^ (c - 1) < 3 + 2 * (i / 3) := by
        have := Nat.pow_pred_clog_lt_self (b := 3) (by norm_num) (x := 3 + 2 * (i / 3)) (by omega)
        rwa [Nat.pred_eq_sub_one] at this
      have hodd : 3 ^ (c - 1) % 2 = 1 := Nat.odd_iff.1 (Odd.pow (by decide))
      have hpow : 3 ^ c = 3 * 3 ^ (c - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hcpos]
      apply le_antisymm
      · rw [Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt (by norm_num)]
        omega
      · rw [Nat.clog_le_iff_le_pow (by norm_num), pow_succ]
        omega

end OMA.A213510Aux

open OMA.S_oeis_a213510 in
theorem OMA.solution : type_of% @OMA.S_oeis_a213510.main := by
  intro n _
  unfold depthSum
  exact Finset.sum_congr rfl (fun i _ => OMA.A213510Aux.depth_eq i)
