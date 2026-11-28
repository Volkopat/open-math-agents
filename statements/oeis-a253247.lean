import Mathlib

/-!
# The period ratio conjecture in A253247

Sources: https://oeis.org/A253247 and https://oeis.org/A175182.
The Lucas sequence A006190 starts at 0, 1 and has recurrence
U(n+2) = 3 U(n+1) + U(n). Its Pisano period modulo m is the least
positive number of steps that returns the state of two successive
terms to (0,1). The conjecture says that the period modulo n²
divided by the period modulo n is 1 precisely when n is 1 or 6.
-/

namespace OMA.S_oeis_a253247

def step (m : ℕ) (state : ZMod m × ZMod m) : ZMod m × ZMod m :=
  (state.2, 3 * state.2 + state.1)

noncomputable def period (m : ℕ) : ℕ := Function.minimalPeriod (step m) (0,1)

theorem main : ∀ n : ℕ, 0 < n →
    ((period (n^2) : ℚ) / (period n : ℚ) = 1 ↔ n = 1 ∨ n = 6) := by
  sorry

end OMA.S_oeis_a253247
