import OMAStatements.S_mo_496222
import Mathlib

open OMA.S_mo_496222

namespace FranelResidue

private def reducedSquare (a : ℕ) : ℕ → ℕ
  | 0 => a % (2 ^ 32)
  | n + 1 => (reducedSquare a n) ^ 2 % (2 ^ 32)

private theorem reducedSquare_cast (a n : ℕ) :
    (reducedSquare a n : ZMod (2 ^ 32)) = (a : ZMod (2 ^ 32)) ^ (2 ^ n) := by
  induction n with
  | zero => simp [reducedSquare, ZMod.natCast_mod]
  | succ n ih =>
      rw [reducedSquare, ZMod.natCast_mod, Nat.cast_pow, ih,
        pow_succ (2 : ℕ) n, pow_mul]

private def residueSum : ℕ :=
  ∑ k ∈ Finset.range 32,
    ((31 : ℕ).choose k * reducedSquare ((31 : ℕ).choose k) 20) % (2 ^ 32)

private theorem residueSum_eq : residueSum % (2 ^ 32) = 2 ^ 31 := by
  decide +kernel

theorem counterexample : ¬ (type_of% @OMA.S_mo_496222.main) := by
  intro h
  have hval : padicValNat 2 (franel 31 (2 ^ 20 + 1)) = 32 := h.1 20 5 (by decide) (by decide)
  have hd : 2 ^ 32 ∣ franel 31 (2 ^ 20 + 1) := by
    rw [← hval]
    exact pow_padicValNat_dvd
  have hc : (franel 31 (2 ^ 20 + 1) : ZMod (2 ^ 32)) = (residueSum : ZMod (2 ^ 32)) := by
    simp only [franel, residueSum, Nat.cast_sum, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [reducedSquare_cast]
    exact (pow_succ _ _).trans (mul_comm _ _)
  have hv := congrArg ZMod.val hc
  simp only [ZMod.val_natCast] at hv
  rw [Nat.dvd_iff_mod_eq_zero.mp hd, residueSum_eq] at hv
  norm_num at hv

end FranelResidue

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_496222.main) :=
  FranelResidue.counterexample