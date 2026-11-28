import OMAReductions.R_Erdos458_erdos_458_R1
import Mathlib

open Finset ArithmeticFunction

theorem OMA.solution : OMA.R_Erdos458_erdos_458_R1.H1 := by
  intro a b hab
  have h n : Real.log (Erdos458.lcm_upto n : ℝ) = Chebyshev.psi n := (Chebyshev.psi_eq_log_lcmUpto n).symm
  rw [h, h, Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast, Nat.floor_natCast,
    ← sum_Ioc_consecutive _ (Nat.zero_le a) hab, add_sub_cancel_left]
