import Mathlib

/-!
# OEIS A285543: Barker's conjectures for the diagonal (origin to corner, base 2) of Rule 35

Source: https://oeis.org/A285543
Formalization: @longling12 (drafted with AI assistance)

Entry A285543 (Robert Price, Apr 20 2017), offset 0: Decimal representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 35, based on the 5-celled von Neumann neighborhood. Initialized with a single
black (ON) cell at stage zero.
Conjectures from Colin Barker, Apr 21 2017:
G.f.: (1 + x - 3*x^2) / ((1 - x)*(1 + x)*(1 - 2*x)*(1 - 2*x^2)).
a(n) = (-1 + (-1)^n + 2^(2+n) - 2^(n/2)*(1+(-1)^n)) / 2.
a(n) = 2*a(n-1) + 3*a(n-2) - 6*a(n-3) - 2*a(n-4) + 4*a(n-5) for n>4.

Modeling notes:
* Rule 35 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 35, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads the diagonal cells (0, 0), (1, 1), ..., (n, n) of the central
  (2n+1) x (2n+1) square as binary digits with (0, 0) most significant and (n, n) least
  significant, as specified by the entry's definition and data (note that Price's %t line in the
  OEIS entry uses the x-axis in base 10).
* In the closed form, (1 + (-1)^n) vanishes for odd n and n / 2 is exact for even n; 2 divides
  the numerator for every n, so integer division over Z is exact. The generating function
  identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in PowerSeries Z.
-/

namespace OMA.S_oeis_a285543

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 35 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 35 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 35 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A285543(n): the diagonal cells (0, 0)..(n, n) of stage n read in binary. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) (i : ℤ)).toNat * 2 ^ (n - i)

/-- Barker's generating function, closed-form, and recurrence conjectures for A285543. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 - 2 * X ^ 2)) =
      1 + X - 3 * X ^ 2 ∧
    (∀ n : ℕ, (a n : ℤ) = (-1 + (-1 : ℤ) ^ n + 2 ^ (2 + n) - 2 ^ (n / 2) * (1 + (-1) ^ n)) / 2) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 2 * a (n - 1) + 3 * a (n - 2) - 6 * a (n - 3) - 2 * a (n - 4) + 4 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a285543
