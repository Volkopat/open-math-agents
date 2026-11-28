import Mathlib

/-!
# OEIS A285834: Barker's conjectures for the diagonal (corner to origin, base 2) of Rule 107

Source: https://oeis.org/A285834
Formalization: @longling12 (drafted with AI assistance)

Entry A285834 (Robert Price, Apr 27 2017), offset 0: Decimal representation of the diagonal from
the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 107, based on the 5-celled von Neumann neighborhood. Initialized with a single
black (ON) cell at stage zero.
Conjectures from Colin Barker, Apr 28 2017:
G.f.: (1+3*x-4*x^2-6*x^3-x^4+4*x^6+6*x^8-28*x^10+16*x^12) /
  ((1-x)*(1+x)*(1-2*x)*(1+2*x)*(1-2*x^2)).
a(n) = 7*a(n-2) - 14*a(n-4) + 8*a(n-6) for n>6.

Modeling notes:
* Rule 107 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 107, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads the diagonal cells (-n, -n), (-n+1, -n+1), ..., (0, 0) of the central
  (2n+1) x (2n+1) square as binary digits with (-n, -n) most significant and (0, 0) least
  significant, as specified by the entry's definition and data (note that Price's %t line in the
  OEIS entry was copied from A278899 and uses the x-axis in base 10).
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z, which is equivalent since D(0) = 1.
-/

namespace OMA.S_oeis_a285834

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 107 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 107 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 107 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A285834(n): the diagonal cells (-n, -n)..(0, 0) of stage n read in binary. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) ((i : ℤ) - n)).toNat * 2 ^ (n - i)

/-- Barker's generating function and recurrence conjectures for A285834. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2)) =
      1 + 3 * X - 4 * X ^ 2 - 6 * X ^ 3 - X ^ 4 + 4 * X ^ 6 + 6 * X ^ 8 - 28 * X ^ 10 +
      16 * X ^ 12 ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 7 * a (n - 2) - 14 * a (n - 4) + 8 * a (n - 6)) := by
  sorry

end OMA.S_oeis_a285834
