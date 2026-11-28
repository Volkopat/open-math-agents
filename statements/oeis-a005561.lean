import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs

/-!
# OEIS A005561

R. J. Mathar's recurrence for column 3 of Guy's square-lattice walk array.
The binomial formula uses a relative index starting at zero. In the OEIS
sequence this column starts at absolute walk length 3.

Sources: https://oeis.org/A005561 and https://oeis.org/A052174
Credit: @wtho704
-/

namespace OMA.S_oeis_a005561

/-- Column y of A052174 at walk length y + t. This is the binomial formula
of A005561 with its zero-based argument t. Pascal's identity gives the
equivalent parity formulas listed for the array A052174. -/
def column (y : ℕ) : ℕ → ℚ
  | 0 => 1
  | t + 1 =>
      let n := y + t + 1
      ((n + 1).choose ((t + 2) / 2) : ℚ) * n.choose ((t + 1) / 2) -
      ((n + 1).choose ((t + 1) / 2) : ℚ) * n.choose (t / 2)

/-- A005561 in its original indexing, with offset 3. -/
def a : ℕ → ℚ
  | 0 | 1 | 2 => 0
  | t + 3 => column 3 t

/-- Mathar's recurrence at every length for which its three terms are defined. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ) - 2) * (n - 3) * (2 * n + 1) * (n + 6) * (n + 5) * a n -
    4 * n * (n + 1) * (2 * (n : ℚ) ^ 2 + 4 * n + 33) * a (n - 1) -
    16 * (n : ℚ) ^ 2 * (n - 1) * (2 * n + 3) * (n + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a005561
