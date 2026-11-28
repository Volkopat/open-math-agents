import OMAStatements.S_oeis_a220181
import Mathlib

open Finset OMA.S_oeis_a220181

theorem OMA.solution : type_of% @OMA.S_oeis_a220181.main := by
  intro p hp n hn
  let _ : Fact p.Prime := ⟨hp⟩
  let m := n + (p - 1)
  have hpow (x : ZMod p) : x ^ m = x ^ n := by
    by_cases hx : x = 0
    · subst x
      rw [zero_pow (show m ≠ 0 by dsimp [m]; omega), zero_pow (by omega : n ≠ 0)]
    · dsimp [m]
      rw [pow_add, ZMod.pow_card_sub_one_eq_one hx, mul_one]
  have castTerm (l k : ℕ) :
      (term l k : ZMod p) =
        (-1 : ZMod p)^k * (-(k : ZMod p))^l *
          ((fwdDiff (1 : ZMod p))^[k] (fun x : ZMod p => x^l) 0) := by
    rw [fwdDiff_iter_eq_sum_shift]
    simp only [term, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast, Int.cast_sum, zsmul_eq_mul, zero_add, nsmul_one]
  have extend :
      (a n : ZMod p) = ∑ k ∈ range (m + 1), (term n k : ZMod p) := by
    simp only [a, Int.cast_sum]
    apply sum_subset
    · exact range_mono (by dsimp [m]; omega)
    · intro k _ hk
      have hn' : n < k := by
        have hh : ¬ k < n + 1 := fun hh => hk (mem_range.mpr hh)
        omega
      rw [castTerm, fwdDiff_iter_pow_eq_zero_of_lt (R := ZMod p) hn', Pi.zero_apply, mul_zero]
  change (a m : ZMod p) = (a n : ZMod p)
  rw [extend]
  simp only [a, Int.cast_sum]
  apply sum_congr rfl
  intro k _
  rw [castTerm, castTerm, hpow]
  rw [show (fun x : ZMod p => x^m) = (fun x => x^n) from funext hpow]