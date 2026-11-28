import Mathlib

/-!
# OEIS A282679: Mathar's conjecture on the x-axes (origin to right edge, base 10) of Rule 499 and Rule 497

Source: https://oeis.org/A282679
Conjecture: R. J. Mathar, Jun 21 2025.
Formalization: @longling12 (drafted with AI assistance)

Entry A282679 (Robert Price, Feb 20 2017), offset 0: Binary representation of the x-axis, from
the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 499, based on the 5-celled von Neumann neighborhood, initialized with
a single black (ON) cell at stage zero.
Formula: Conjecture: a(n) = A282675(n) for n>=2. - R. J. Mathar, Jun 21 2025.
Entry A282675 (Robert Price, Feb 20 2017), offset 0, is defined in the same words with Rule 497.

Modeling notes:
* Outer-totalistic 5-cell von Neumann Rules 499 and 497 on Z^2 started from a single ON cell at
  (0, 0).
* At stage n, cells (0, 0), (1, 0), ..., (n, 0) are read as digits in base 10 with (0, 0) most
  significant, matching FromDigits[..., 10] in the entries' Mathematica programs, giving
  a(1) = 10 for Rule 499 and A282675(1) = 0 for Rule 497.
-/

namespace OMA.S_oeis_a282679

/-- One step of outer-totalistic Rule r on the 5-cell von Neumann neighborhood. -/
def step (r : ℕ) (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit r ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule r started from a single ON cell at the origin. -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step r (state r n)

/-- Cells (0, 0)..(n, 0) of stage n of Rule r read in base 10 from origin to right edge. -/
def xaxisRight10 (r n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state r n (i : ℤ) 0).toNat * 10 ^ (n - i)

/-- A282679(n): x-axis from origin to right edge in base 10 for Rule 499. -/
def a (n : ℕ) : ℕ := xaxisRight10 499 n

/-- A282675(n): x-axis from origin to right edge in base 10 for Rule 497. -/
def A282675 (n : ℕ) : ℕ := xaxisRight10 497 n

/-- Mathar's conjecture: A282679(n) = A282675(n) for n >= 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n → a n = A282675 n := by
  sorry

end OMA.S_oeis_a282679
