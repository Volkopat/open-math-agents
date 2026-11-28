import OMAStatements.S_oeis_a081658
import Mathlib

/-!
# OEIS A081658: for prime `n`, every interior entry of row `n` is divisible by `n`

`T(n, k) = C(n, k) · E(k)` with `E(k)` an integer, and a prime `n` divides `C(n, k)` for
`1 ≤ k ≤ n - 1`.
-/

open OMA.S_oeis_a081658

theorem OMA.solution : type_of% @OMA.S_oeis_a081658.main := by
  intro n k hn hk1 hk2
  have hlt : k < n := by
    have := hn.two_le
    omega
  have hdvd : n ∣ n.choose k := hn.dvd_choose_self (by omega) hlt
  unfold T
  exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hdvd) _
