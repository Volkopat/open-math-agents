import Mathlib

/-!
# OEIS A280610: Barker's conjectures for the x-axis (origin to right edge, base 2) of Rule 294

Source: https://oeis.org/A280610
Formalization: @longling12 (drafted with AI assistance)

Entry A280610 (Robert Price, Jan 06 2017), offset 0: Decimal representation of the x-axis, from
the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 294, based on the 5-celled von Neumann neighborhood. Initialized with
a single black (ON) cell at stage zero.
Conjectures from Colin Barker, Jan 07 2017:
a(n) = 4 - 3*(-1)^n + 2^n for n>3.
a(n) = 2*a(n-1) + a(n-2) - 2*a(n-3) for n>4.

Modeling notes:
* Rule 294 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 294, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads the cells (0, 0), (1, 0), ..., (n, 0) as binary digits with
  (0, 0) most significant and (n, 0) least significant, matching FromDigits[..., 2] in the
  entry's Mathematica program.
-/

namespace OMA.S_oeis_a280610

/-- One step of the two-dimensional outer totalistic Rule 294 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 294 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 294 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A280610(n): the cells (0, 0)..(n, 0) of stage n read in binary from origin to right edge. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) 0).toNat * 2 ^ (n - i)

/-- Barker's closed-form and recurrence conjectures for A280610. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 4 - 3 * (-1 : ℤ) ^ n + 2 ^ n) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a280610
