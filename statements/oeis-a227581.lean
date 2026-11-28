import Mathlib

/-!
# A227581: the diagonal of the harmonic array

The array entry at positive indices m and n is the least natural number k
for which H(m) + H(n) - H(m*n+k) is less than Euler's constant.
The four claims concern the diagonal, the two harmonic sums bracketing the
constant, and the floors of the reciprocals of their positive gaps.
A227582 is encoded independently by its published recurrence and initial terms.
The fourth claim is proved by AlphaProof Nexus in the companion A227582 file.

Sources:
https://oeis.org/A227581
https://oeis.org/A227582
https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/OEIS/oeis_227582_conjecture_0.lean
-/

namespace OMA.S_oeis_a227581

open Real

/-- The least shift at which the harmonic difference falls below Euler's constant. -/
noncomputable def r (m n : ℕ) : ℕ :=
  sInf {k : ℕ | (harmonic m : ℝ) + (harmonic n : ℝ) -
    (harmonic (m * n + k) : ℝ) < eulerMascheroniConstant}

/-- The recurrence for A227582, in increasing order of the shifts. -/
def a227582Recurrence : LinearRecurrence ℤ where
  order := 7
  coeffs := ![1, -2, 1, 0, 0, -1, 2]

/-- The one-indexed sequence A227582, with a dummy zeroth term. -/
noncomputable def a227582 (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    (a227582Recurrence.mkSol ![2, 7, 14, 23, 35, 50, 67] (n - 1)).toNat

theorem main : ∀ n : ℕ, 1 ≤ n →
    r n n = n ∧
    (2 * (harmonic n : ℝ) - (harmonic (n * n + n) : ℝ) < eulerMascheroniConstant ∧
      eulerMascheroniConstant < 2 * (harmonic n : ℝ) - (harmonic (n * n + n - 1) : ℝ)) ∧
    ⌊1 / (eulerMascheroniConstant - 2 * (harmonic n : ℝ) +
      (harmonic (n * n + n) : ℝ))⌋₊ = 6 * n * (n + 1) ∧
    ⌊1 / (2 * (harmonic n : ℝ) - (harmonic (n * n + n - 1) : ℝ) -
      eulerMascheroniConstant)⌋₊ = a227582 n := by
  sorry

end OMA.S_oeis_a227581
