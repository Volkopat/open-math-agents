import Mathlib.Init

/-!
# Parity of the coefficients in OEIS A368635

Paul D. Hanna defines the integer series A by
A(x) = 1 + 3x A(x)^2 − 2x A(−x)^2. The definitions below take its
coefficients starting at zero, using the Cauchy product. The theorem states
that the term at index n is odd exactly when n is one less than a power of two.

Source: https://oeis.org/A368635
-/

namespace OMA.S_oeis_a368635

/-- Cauchy product on indices from `s` through `s+n`; at s = 0 this is
the coefficient of x^n in the square of the generating function. -/
def squareCoeff (a : Nat → Int) (s n : Nat) : Int :=
  ((List.range (n + 1)).map fun i => a (s + i) * a (s + (n - i))).sum

/-- The coefficient of x^(n+1) on the right of the generating function equation. -/
def next (a : Nat → Int) (n : Nat) : Int :=
  3 * squareCoeff a 0 n - 2 * squareCoeff (fun i => (-1 : Int) ^ i * a i) 0 n

/-- The sequence, constructed recursively. Computing the next coefficient
uses only the preceding coefficients, up to and including index n. -/
def coeff : Nat → Int
  | 0 => 1
  | n + 1 => next (fun i => if _h : i ≤ n then coeff i else 0) n
termination_by n => n
decreasing_by omega

/-- The parity conjecture for OEIS A368635, including the constant term. -/
theorem main : ∀ n : Nat, coeff n % 2 = 1 ↔ ∃ k : Nat, n + 1 = 2 ^ k := by
  sorry

end OMA.S_oeis_a368635
