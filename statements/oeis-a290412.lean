import Mathlib

/-!
# OEIS A290412: Barker's conjectures for the diagonal (corner to origin, base 10) of Rule 785

Source: https://oeis.org/A290412
Conjectures: Colin Barker, Jul 31 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A290412 (Robert Price, Jul 30 2017), offset 0: Binary representation of the diagonal from the
corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton defined
by Rule 785, based on the 5-celled von Neumann neighborhood. Initialized with a single black (ON)
cell at stage zero.
Conjectures from Colin Barker, Jul 31 2017:
G.f.: (1 - 10*x^2 + 100*x^3 - 100*x^4 + x^5 - 11*x^6 + 110*x^8 - 100*x^9) /
  ((1 - x)*(1 + x)*(1 - 10*x)*(1 - 10*x^2)).
a(n) = 10*a(n-1) + 11*a(n-2) - 110*a(n-3) - 10*a(n-4) + 100*a(n-5) for n>6.

Modeling notes:
* Rule 785 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 785, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* Following %N and the sequence data, a(n) reads the diagonal cells (-n, -n), ..., (0, 0) of the
  central (2n+1) x (2n+1) square as decimal digits with (-n, -n) most significant and (0, 0) least
  significant (the last line of %t in the OEIS entry extracts an x-axis row instead).
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z since D(0) = 1; the recurrence is stated over Z.
-/

namespace OMA.S_oeis_a290412

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 785 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 785 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 785 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A290412(n): the diagonal cells (-n, -n)..(0, 0) of stage n read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) ((i : ℤ) - n)).toNat * 10 ^ (n - i)

/-- Barker's generating function and recurrence conjectures for A290412. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 - 10 * X ^ 2)) =
      1 - 10 * X ^ 2 + 100 * X ^ 3 - 100 * X ^ 4 + X ^ 5 - 11 * X ^ 6 + 110 * X ^ 8 -
      100 * X ^ 9 ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 10 * a (n - 1) + 11 * a (n - 2) - 110 * a (n - 3) - 10 * a (n - 4) +
        100 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a290412
