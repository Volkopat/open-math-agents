import OMAReductions.R_Erdos11_erdos_11_R1

/-!
Proof of `OMA.R_Erdos11_erdos_11_R1.H2`.
If every odd `n > 1` is a squarefree number plus a power of two, then this holds for all
sufficiently large odd `n`: the eventual statement only needs `n > 1`, which holds eventually.
-/

open Filter in
theorem OMA.solution : OMA.R_Erdos11_erdos_11_R1.H2 := by
  intro h
  filter_upwards [eventually_gt_atTop 1] with n hn hodd
  exact h n hodd hn
