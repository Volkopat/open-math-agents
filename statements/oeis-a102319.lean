import Mathlib

/-!
# Two recurrences for the mean binomial transform of the central binomial numbers

Paul Barry defined A102319. R. J. Mathar conjectured the two recurrences on February 20, 2015.
Source: https://oeis.org/A102319 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson
-/

namespace OMA.S_oeis_a102319

/-- The binomial transform with weight `s` of the central binomial coefficients. -/
def transform (s : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * k.centralBinom * s ^ (n - k)

/-- Average of the ordinary and inverse binomial transforms, indexed from zero. -/
def a (n : ℕ) : ℚ := (transform 1 n + transform (-1) n) / 2

/-- Mathar's order-six recurrence, with all indices in the sequence domain. -/
def orderSix (u : ℕ → ℚ) (n : ℕ) : Prop :=
  let x : ℚ := n
  x * (x - 1) * u n - 4 * (x - 1) * (3*x - 4) * u (n-1)
    + (53*x^2 - 221*x + 232) * u (n-2) + 8 * (-13*x^2 + 85*x - 134) * u (n-3)
    + (51*x^2 - 563*x + 1308) * u (n-4) + 4 * (29*x - 93) * (x - 4) * u (n-5)
    - 105 * (x - 4) * (x - 5) * u (n-6) = 0

/-- Mathar's order-four recurrence. -/
def orderFour (u : ℕ → ℚ) (n : ℕ) : Prop :=
  let x : ℚ := n
  x * (x - 1) * (12*x^2 - 48*x + 41) * u n
    - 8 * (x - 1) * (12*x^3 - 54*x^2 + 65*x - 17) * u (n-1)
    + 2 * (84*x^4 - 504*x^3 + 1025*x^2 - 775*x + 131) * u (n-2)
    + 8 * (x - 2) * (12*x^3 - 54*x^2 + 65*x - 20) * u (n-3)
    - 15 * (x - 2) * (x - 3) * (12*x^2 - 24*x + 5) * u (n-4) = 0

theorem main : (∀ n, 6 ≤ n → orderSix a n) ∧ (∀ n, 4 ≤ n → orderFour a n) := by
  sorry

end OMA.S_oeis_a102319
