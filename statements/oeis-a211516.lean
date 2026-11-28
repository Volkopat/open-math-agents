import Mathlib

/-!
# A211516: Number of ordered triples (w,x,y) with all terms in {1,...,n} and w^2=x+y.

Source: https://oeis.org/A211516
Credit: @agchua

Velin Yanev (Nov 16 2021), in the formula section of A211516:
  Conjecture: a(n) = -(2*n + 5/3)*w(n) + w(n)^2 + (2/3)*w(n)^3 + (2*n + 5/6)*w(2*n)
  - (1/2)*w(2*n)^2 - (1/3)*w(2*n)^3, where w = A000196.
A000196(n) = floor(sqrt(n)) is Nat.sqrt n. The sequence has offset 0 and the formula involves
only a(n) itself, so the claim is stated for every n ≥ 0. The right side has fractional
coefficients, so both sides are compared in ℚ.
-/

namespace OMA.S_oeis_a211516

/-- A211516(n): the number of triples (w, x, y) in {1, ..., n}^3 with w^2 = x + y. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun t : ℕ × ℕ × ℕ => t.1 ^ 2 = t.2.1 + t.2.2)).card

/-- Yanev's conjecture, with w = A000196 = Nat.sqrt. -/
theorem main : ∀ n : ℕ, (a n : ℚ) =
    -(2 * (n : ℚ) + 5 / 3) * (Nat.sqrt n : ℚ) + (Nat.sqrt n : ℚ) ^ 2
      + (2 / 3) * (Nat.sqrt n : ℚ) ^ 3 + (2 * (n : ℚ) + 5 / 6) * (Nat.sqrt (2 * n) : ℚ)
      - (1 / 2) * (Nat.sqrt (2 * n) : ℚ) ^ 2 - (1 / 3) * (Nat.sqrt (2 * n) : ℚ) ^ 3 := by
  sorry

end OMA.S_oeis_a211516
