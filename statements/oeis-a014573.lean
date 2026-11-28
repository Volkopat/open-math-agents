import Mathlib

/-!
# A014573: Smallest k such that phi(x) = k has exactly n solutions, n>=0 with Carmichael conjecture.

Source: https://oeis.org/A014573
Credit: @EtienneLefranc

OEIS A014573 lists, for each `n ≥ 0`, the smallest `k` such that the equation `φ(x) = k` has
exactly `n` solutions in positive integers `x`. The entry records: Carmichael conjectured that
no term exists for `n = 1`, i.e. no value `k` is attained by Euler's totient function exactly
once. Solutions `x` range over positive integers, as in OEIS (Mathlib sets `φ 0 = 0`, so `x = 0`
is excluded explicitly). `Set.encard` counts the solutions without assuming finiteness.
-/

namespace OMA.S_oeis_a014573

/-- The set of positive integers `x` with `φ(x) = k`. -/
def solutions (k : ℕ) : Set ℕ := {x : ℕ | 0 < x ∧ Nat.totient x = k}

/-- Carmichael's totient conjecture as stated in OEIS A014573: the sequence has no term for
`n = 1`, i.e. there is no `k` for which `φ(x) = k` has exactly one solution. -/
theorem main : ¬ ∃ k : ℕ, (solutions k).encard = 1 := by
  sorry

end OMA.S_oeis_a014573
