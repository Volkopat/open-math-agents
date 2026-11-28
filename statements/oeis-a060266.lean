import Mathlib

/-!
# Rocchelli's conjecture on the distance from an even number to the following prime

Source: https://oeis.org/A060266
Credit: @pyaf
-/

namespace OMA.S_oeis_a060266

/-- For n ≥ 1, the distance from 2n to the first prime strictly greater than 2n. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (2 * n + 1)) - 2 * n

open Filter Topology

theorem main :
    Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.Icc 1 n, (a k : ℝ)) /
        (∑ k ∈ Finset.Icc 1 n, Real.log (2 * (k : ℝ)))) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a060266
