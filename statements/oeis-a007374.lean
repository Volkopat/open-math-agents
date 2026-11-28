import Mathlib

/-!
# A007374: Smallest k such that phi(x) = k has exactly n solutions, n>=2.

Source: https://oeis.org/A007374
Credit: @divmxnd0x

Conjecture (Carmichael's totient conjecture, stated in A007374): there is no `k` such that
`phi(x) = k` has a unique solution `x` (so `a(1)` does not exist).

Formalization notes:
* Solutions `x` are positive integers, as in the OEIS (Mathlib's `Nat.totient 0 = 0`, and `x = 0`
  is excluded).
-/

namespace OMA.S_oeis_a007374

/-- Carmichael's totient conjecture: for no `k` does `phi(x) = k` have exactly one positive
solution `x`. -/
theorem main : ∀ k : ℕ, ¬ ∃! x : ℕ, 0 < x ∧ Nat.totient x = k := by
  sorry

end OMA.S_oeis_a007374
