import Mathlib

/-!
# OEIS A287193: Barker's conjectures for the diagonal (origin to corner, base 2) of Rule 253

Source: https://oeis.org/A287193
Conjectures: Colin Barker, Nov 22 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A287193 (Robert Price, May 21 2017), offset 0: Decimal representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 253, based on the 5-celled von Neumann neighborhood. Initialized with a single
black (ON) cell at stage zero.
Conjectures from Colin Barker, Nov 22 2017:
G.f.: (1 + x - 5*x^2 + 2*x^3 + 28*x^4 - 24*x^6) / ((1 - x)*(1 + x)*(1 - 2*x)*(1 + 2*x)).
a(n) = (1/4)*(-2 + (-2)^n + 2*(-1)^n + 5*2^n) for n>2.
a(n) = 5*a(n-2) - 4*a(n-4) for n>4.

Modeling notes:
* Rule 253 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 253, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* Following %N and the sequence data, a(n) reads the diagonal cells (0, 0), ..., (n, n) of the
  central (2n+1) x (2n+1) square as binary digits with (0, 0) most significant and (n, n) least
  significant (the last line of %t in the OEIS entry extracts an x-axis row in base 10 instead).
* The closed form has rational coefficient 1/4 and is stated over Q; the recurrence is stated over
  Z, and the generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z since D(0) = 1.
-/

namespace OMA.S_oeis_a287193

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 253 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 253 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 253 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A287193(n): the diagonal cells (0, 0)..(n, n) of stage n read in binary. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) (i : ℤ)).toNat * 2 ^ (n - i)

/-- Barker's generating function, closed form, and recurrence conjectures for A287193. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + X - 5 * X ^ 2 + 2 * X ^ 3 + 28 * X ^ 4 - 24 * X ^ 6 ∧
    (∀ n : ℕ, 2 < n →
      (a n : ℚ) = (1 / 4 : ℚ) * (-2 + (-2 : ℚ) ^ n + 2 * (-1 : ℚ) ^ n + 5 * 2 ^ n)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a287193
