import Mathlib

/-!
# OEIS A069548 — odd values of a Möbius-weighted divisor sum

Benoit Cloitre's sequence lists the prime values of the divisor sum below.
Alonso del Arte conjectured the necessary condition on its index stated here.
Charles R. Greathouse IV records it in the OEIS entry. His intermediate claim
about the parity of the squarefree correction has an exception at powers of two.

Source: https://oeis.org/A069548
OEIS Foundation, CC BY-SA 4.0. Lean formalization: @rifter0418.
-/

namespace OMA.S_oeis_a069548

/-- The factor multiplying each divisor in the numerator is six. Integer division
is exact since the Möbius value is one of -1, 0, and 1. -/
def summand (d : ℕ) : ℤ :=
  6 * (d : ℤ) / (2 + ArithmeticFunction.moebius d)

/-- The function whose prime values form A069548. -/
def divisorSum (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, summand d

/-- If an index greater than one gives an odd value, it is a square or twice a square. -/
theorem main :
    ∀ n : ℕ, 1 < n → Odd (divisorSum n) →
      IsSquare n ∨ ∃ r : ℕ, n = 2 * r ^ 2 := by
  sorry

end OMA.S_oeis_a069548
