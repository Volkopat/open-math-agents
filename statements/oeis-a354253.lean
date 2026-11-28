import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Totient

/-!
# Eventual periods of OEIS A354253

Peter Bala conjectured that, for each positive modulus, the eventual period of
this sequence divides Euler's totient of the modulus. The finite Stirling sum
below is the formula given in the OEIS entry, indexed from zero.

Source: https://oeis.org/A354253
Credit: @DomTheDeveloper
-/

namespace OMA.S_oeis_a354253

/-- The coefficient of `x^n / n!` in `1 / sqrt(9 - 8 * exp(x))`. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1),
    2 ^ j * (2 * j).factorial * Nat.stirlingSecond n j / j.factorial

/-- Some positive period of the tail divides the totient. -/
theorem main :
    ∀ k : ℕ, 0 < k →
      ∃ d : ℕ, 0 < d ∧ d ∣ k.totient ∧
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + d) % k = a n % k := by
  sorry

end OMA.S_oeis_a354253
