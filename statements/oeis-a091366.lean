import Mathlib

/-!
# OEIS A091366: primes whose digit-cube sum is prime have relative density 0

Source: https://oeis.org/A091366
Primes `p` such that the sum of the cubes of the decimal digits of `p` is prime. Conjecture
(Greathouse IV, 2010): the relative density of this sequence among the primes is `0`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a091366

open Filter Topology

/-- Sum of the cubes of the decimal digits. -/
def s3 (n : ℕ) : ℕ := ((Nat.digits 10 n).map fun d => d ^ 3).sum

theorem main :
    Tendsto (fun x : ℕ =>
        (((Finset.range (x + 1)).filter fun p => p.Prime ∧ (s3 p).Prime).card : ℝ) /
          ((Finset.range (x + 1)).filter Nat.Prime).card) atTop (𝓝 0) := by
  sorry

end OMA.S_oeis_a091366
