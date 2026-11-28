import Mathlib

/-!
# OEIS A005597 and the Hardy–Littlewood prime-pair asymptotic

Source: https://oeis.org/A005597
Original conjecture: https://doi.org/10.1007/BF02403921

For each fixed positive `m`, count primes `p ≤ n` such that `p + 2m` is also prime.
The conjectured asymptotic is `2 C₂ Li₂(n)` times the product of `(p−1)/(p−2)`
over the odd prime divisors of `m`. Here `C₂` is the infinite product over odd
primes shown in the OEIS entry. The integral uses the range from 2 to `n` for
`n ≥ 2`, and is extended by zero below 2.
-/

namespace OMA.S_oeis_a005597

open Filter MeasureTheory
open scoped Topology

/-- The twin prime constant, before the factor of two in the pair asymptotic. -/
noncomputable def twinPrimeConstant : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.val : ℝ) - 1) ^ 2)

/-- The finite correction associated with half of the gap. -/
noncomputable def gapCorrection (m : ℕ) : ℝ :=
  ∏ p ∈ m.primeFactors.erase 2, ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- The lower endpoint of each ordered prime pair is at most `n`. -/
def pairCount (m n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun p => p.Prime ∧ (p + 2 * m).Prime).card

/-- The logarithmic integral with integrand `1 / (log x)^2`. -/
noncomputable def liTwo (n : ℕ) : ℝ :=
  ∫ x in (2 : ℝ)..max 2 (n : ℝ), 1 / Real.log x ^ 2

/-- The Hardy–Littlewood asymptotic for every fixed positive even gap. -/
theorem main : ∀ m : ℕ, 1 ≤ m →
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (pairCount m n : ℝ))
      (fun n : ℕ => (2 * twinPrimeConstant * gapCorrection m) * liTwo n) := by
  sorry

end OMA.S_oeis_a005597
