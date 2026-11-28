import Mathlib

/-!
# OEIS A285833: Barker's conjectures for the diagonal (origin to corner, base 10) of Rule 107

Source: https://oeis.org/A285833
Formalization: @longling12 (drafted with AI assistance)

Entry A285833 (Robert Price, Apr 27 2017), offset 0: Binary representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 107, based on the 5-celled von Neumann neighborhood. Initialized with a single
black (ON) cell at stage zero.
Conjectures from Colin Barker, Apr 28 2017:
G.f.: (1 + 11*x - x^2 - 110*x^3 - 10000*x^4 + 10000*x^6 + 11000000*x^8 - 111000000*x^10
  + 100000000*x^12) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)*(1 - 10*x^2)).
a(n) = 111*a(n-2) - 1110*a(n-4) + 1000*a(n-6) for n>6.

Modeling notes:
* Rule 107 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 107, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads the diagonal cells (0, 0), (1, 1), ..., (n, n) of the central
  (2n+1) x (2n+1) square in base 10 with (0, 0) most significant and (n, n) least significant,
  as specified by the entry's definition and data (note that the last line of %t in the OEIS
  entry was copied from A278899 and extracts the x-axis rather than the diagonal).
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z, which is equivalent since D(0) = 1.
-/

namespace OMA.S_oeis_a285833

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 107 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 107 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 107 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A285833(n): the diagonal cells (0, 0)..(n, n) of stage n read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) (i : ℤ)).toNat * 10 ^ (n - i)

/-- Barker's generating function and recurrence conjectures for A285833. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      1 + 11 * X - X ^ 2 - 110 * X ^ 3 - 10000 * X ^ 4 + 10000 * X ^ 6 + 11000000 * X ^ 8 -
      111000000 * X ^ 10 + 100000000 * X ^ 12 ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 111 * a (n - 2) - 1110 * a (n - 4) + 1000 * a (n - 6)) := by
  sorry

end OMA.S_oeis_a285833
