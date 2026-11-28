import OMAReductions.R_mo_280192_R1

/-!
Step `mo-280192.R1.H1`: the finite range `2 ≤ k ≤ 4096` of MathOverflow 280192.

For `k = i + 2` and `m = (3^k - 1) / 2^k + 1`, the least multiple `2^k * m` of `2^k` that is at
least `3^k` leaves room for `m` itself: `3^k + m ≤ 2^k * m`. Writing `3^k = q * 2^k + r`, this is
the ideal-Waring condition `q + r < 2^k`. All 4095 cases are checked by evaluation in the Lean
kernel (`decide +kernel`; the 4095-deep decision procedure needs a larger `maxRecDepth`):
no `native_decide`, no extra axioms.
-/

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_mo_280192_R1.H1 := by
  unfold OMA.R_mo_280192_R1.H1
  decide +kernel
