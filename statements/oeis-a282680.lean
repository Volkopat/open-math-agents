import Mathlib

/-!
# OEIS A282680: Mathar's conjecture on the x-axes (left edge to origin, base 2) of Rule 499 and Rule 497

Source: https://oeis.org/A282680
Conjecture: R. J. Mathar, Jun 21 2025.
Formalization: @longling12 (drafted with AI assistance)

Entry A282680 (Robert Price, Feb 20 2017), offset 0: Decimal representation of the x-axis, from
the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 499, based on the 5-celled von Neumann neighborhood, initialized with
a single black (ON) cell at stage zero.
Formula: Conjecture: a(n) = A282676(n) for n>=2. - R. J. Mathar, Jun 21 2025.
Entry A282676 (Robert Price, Feb 20 2017), offset 0, is defined in the same words with Rule 497.

Modeling notes:
* Outer-totalistic 5-cell von Neumann Rules 499 and 497 on Z^2 started from a single ON cell at
  (0, 0).
* At stage n, cells (-n, 0), (-n + 1, 0), ..., (0, 0) are read as binary digits (base 2) with
  (-n, 0) most significant, matching FromDigits[..., 2] in the entries' Mathematica programs,
  giving a(1) = 1 for Rule 499 and A282676(1) = 0 for Rule 497.
-/

namespace OMA.S_oeis_a282680

/-- One step of outer-totalistic Rule r on the 5-cell von Neumann neighborhood. -/
def step (r : ℕ) (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit r ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule r started from a single ON cell at the origin. -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step r (state r n)

/-- Cells (-n, 0)..(0, 0) of stage n of Rule r read in base 2 from left edge to origin. -/
def xaxisLeft2 (r n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state r n ((i : ℤ) - n) 0).toNat * 2 ^ (n - i)

/-- A282680(n): x-axis from left edge to origin in base 2 for Rule 499. -/
def a (n : ℕ) : ℕ := xaxisLeft2 499 n

/-- A282676(n): x-axis from left edge to origin in base 2 for Rule 497. -/
def A282676 (n : ℕ) : ℕ := xaxisLeft2 497 n

/-- Mathar's conjecture: A282680(n) = A282676(n) for n >= 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n → a n = A282676 n := by
  sorry

end OMA.S_oeis_a282680
