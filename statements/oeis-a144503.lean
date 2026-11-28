import Mathlib

/-!
# An exponential integral for the gift exchange sequence A144503

Source: https://oeis.org/A144503
Credit: @VestigeClub

A144503 sums the antidiagonals of the gift exchange array A144502.
The recurrence and initial values recorded by G. C. Greubel in 2023
characterize the sequence independently of Velin Yanev's 2026 integral
conjecture. The integer index of the Chebyshev polynomial includes n = 0,
when the polynomial of index -1 vanishes. The integral is over the positive
real half-line, with respect to Lebesgue measure.
-/

namespace OMA.S_oeis_a144503

def giftExchange : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | k + 2 => 2 * ((k : ℤ) + 1) * giftExchange (k + 1) + giftExchange k - 2 * (k : ℤ)

theorem main : ∀ n : ℕ, (giftExchange n : ℝ) =
    1 + ∫ x in Set.Ioi (0 : ℝ), (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)).eval (x + 1) /
      Real.exp x := by
  sorry

end OMA.S_oeis_a144503
