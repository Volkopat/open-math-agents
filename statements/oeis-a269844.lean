import Mathlib

/-!
# Relative density of primes from consecutive squarefree integers

Charles R. Greathouse IV conjectures that OEIS A269844 has relative density
`4 * C₂ / π²` among the primes, where `C₂` is the twin prime constant.
The entry lists the prime sums above 3.

Sources: https://oeis.org/A269844 and https://oeis.org/A005597
(OEIS Foundation, CC BY-SA 4.0).
Credit: @wtho704
-/

namespace OMA.S_oeis_a269844

open Filter
open scoped Topology

/-- The Euler product over odd primes defining the twin prime constant. -/
noncomputable def twinPrimeConstant : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
    (1 - 1 / ((p.val : ℝ) - 1) ^ 2)

open Classical in
/-- The terms of A269844 at most `x`. -/
noncomputable def count (x : ℕ) : ℕ :=
  ((Nat.primesBelow (x + 1)).filter fun p =>
    3 < p ∧ ∃ k : ℕ, p = k + (k + 1) ∧ Squarefree k ∧ Squarefree (k + 1)).card

theorem main :
    Tendsto (fun x : ℕ ↦ (count x : ℝ) / (Nat.primeCounting x : ℝ))
      atTop (𝓝 (4 * twinPrimeConstant / Real.pi ^ 2)) := by
  sorry

end OMA.S_oeis_a269844
