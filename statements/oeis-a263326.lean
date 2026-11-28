import Mathlib

/-!
# Fractional parts of shifted reciprocal-divisor sums (OEIS A263326)

Source: https://oeis.org/A263326 (OEIS Foundation, CC BY-SA 4.0).
The conjecture was proposed by Zhi-Wei Sun in 2015. The sequence itself
uses k = s = 1, but the conjecture quantifies over all positive k and s.

`Set.Ioi 0` restricts injectivity to positive integers. For a rational
number, a zero `Int.fract` means that the number is integral.

Known status: Appendix A of Tom Adamczewski's *OEIS Open*
(https://arxiv.org/abs/2608.11941) reports that the sums at 5 and 1829
coincide for k = 31 and s = 1. We state the original conjecture in full.
-/

namespace OMA.S_oeis_a263326

/-- The sum of the reciprocals of the shifted divisors raised to the power s. -/
def shiftedDivisorSum (k s n : ℕ) : ℚ :=
  ∑ d ∈ n.divisors, (1 : ℚ) / ((d : ℚ) + k) ^ s

theorem main : ∀ k s : ℕ, 0 < k → 0 < s →
    Set.InjOn (fun n : ℕ => Int.fract (shiftedDivisorSum k s n)) (Set.Ioi 0) ∧
    ∀ n : ℕ, 0 < n → Int.fract (shiftedDivisorSum k s n) ≠ 0 := by
  sorry

end OMA.S_oeis_a263326
