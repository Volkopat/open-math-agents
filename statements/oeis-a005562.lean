import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs

/-!
# OEIS A005562

R. J. Mathar's recurrence for column 4 of Guy's square-lattice walk array.
The binomial formula uses a relative index starting at zero. In the OEIS
sequence this column starts at absolute walk length 4.

Sources: https://oeis.org/A005562 and https://oeis.org/A052174
Credit: @wtho704
-/

namespace OMA.S_oeis_a005562

/-- Column y of A052174 at walk length y + t. This is the binomial formula
of A005562 with its zero-based argument t. Pascal's identity gives the
equivalent parity formulas listed for the array A052174. -/
def column (y : ℕ) : ℕ → ℚ
  | 0 => 1
  | t + 1 =>
      let n := y + t + 1
      ((n + 1).choose ((t + 2) / 2) : ℚ) * n.choose ((t + 1) / 2) -
      ((n + 1).choose ((t + 1) / 2) : ℚ) * n.choose (t / 2)

/-- A005562 in its original indexing, with offset 4. -/
def a : ℕ → ℚ
  | 0 | 1 | 2 | 3 => 0
  | t + 4 => column 4 t

/-- Mathar's recurrence at every length for which its three terms are defined. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℚ) - 3) * (n - 4) * (2 * n + 1) * (n + 7) * (n + 6) * a n -
    4 * n * (n + 1) * (2 * (n : ℚ) ^ 2 + 4 * n + 51) * a (n - 1) -
    16 * (n : ℚ) ^ 2 * (n - 1) * (2 * n + 3) * (n + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a005562
