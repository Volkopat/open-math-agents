import Mathlib

/-!
# The Bateman–Horn prediction for OEIS A053182

The sequence consists of primes `p` for which `p ^ 2 + p + 1` is also prime.
Bateman and Horn tested their prediction on this pair of polynomials in
[Math. Comp. 16 (1962), 363–367](https://doi.org/10.1090/S0025-5718-1962-0148632-7).
The sequence is [A053182](https://oeis.org/A053182) and its Euler product is
[A188596](https://oeis.org/A188596).
-/

namespace OMA.S_oeis_a053182

open Asymptotics Filter Topology

/-- The number of terms of A053182 at most `x`. -/
noncomputable def count (x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ (p ^ 2 + p + 1).Prime).card

/-- The number of residues at which either polynomial vanishes modulo `q`. -/
def vanishingResidues (q : ℕ) : ℕ :=
  ((Finset.range q).filter fun r => q ∣ r * (r ^ 2 + r + 1)).card

/-- The Euler product truncated to primes below `N`, in increasing prime order. -/
noncomputable def partialProduct (N : ℕ) : ℝ :=
  ∏ q ∈ Nat.primesBelow N,
    (1 - (vanishingResidues q : ℝ) / q) / (1 - 1 / (q : ℝ)) ^ 2

/-- The factor `1 / 2` is the reciprocal of the product of the two degrees. -/
theorem main :
    ∃ C : ℝ, 0 < C ∧ Tendsto partialProduct atTop (𝓝 C) ∧
      (fun x : ℝ => (count x : ℝ)) ~[atTop]
        (fun x : ℝ => C / 2 * (∫ t in 2..x, 1 / (Real.log t) ^ 2)) := by
  sorry

end OMA.S_oeis_a053182
