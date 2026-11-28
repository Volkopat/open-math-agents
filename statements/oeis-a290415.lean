import Mathlib

/-!
# OEIS A290415: Barker's conjectures for the diagonal (origin to corner, base 2) of Rule 785

Source: https://oeis.org/A290415
Conjectures: Colin Barker, Jul 31 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A290415 (Robert Price, Jul 30 2017), offset 0: Decimal representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 785, based on the 5-celled von Neumann neighborhood. Initialized with a single
black (ON) cell at stage zero.
Conjectures from Colin Barker, Jul 31 2017:
G.f.: (1 - 2*x^2 + 2*x^3 - 4*x^4 + 32*x^5 - 96*x^6 + 192*x^8 - 128*x^9) /
  ((1 - x)*(1 - 2*x)*(1 + 2*x)*(1 - 2*x^2)).
a(n) = a(n-1) + 6*a(n-2) - 6*a(n-3) - 8*a(n-4) + 8*a(n-5) for n>6.

Modeling notes:
* Rule 785 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 785, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* Following %N and the sequence data, a(n) reads the diagonal cells (0, 0), ..., (n, n) of the
  central (2n+1) x (2n+1) square as binary digits with (0, 0) most significant and (n, n) least
  significant (the last line of %t in the OEIS entry extracts an x-axis row in base 10 instead).
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z since D(0) = 1; the recurrence is stated over Z.
-/

namespace OMA.S_oeis_a290415

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 785 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 785 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 785 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A290415(n): the diagonal cells (0, 0)..(n, n) of stage n read in binary. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) (i : ℤ)).toNat * 2 ^ (n - i)

/-- Barker's generating function and recurrence conjectures for A290415. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2)) =
      1 - 2 * X ^ 2 + 2 * X ^ 3 - 4 * X ^ 4 + 32 * X ^ 5 - 96 * X ^ 6 + 192 * X ^ 8 -
      128 * X ^ 9 ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - 8 * a (n - 4) + 8 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a290415
