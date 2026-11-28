import Mathlib

/-!
# OEIS A283713: Barker's conjectures for the x-axis (origin to right edge, base 10) of Rule 758

Source: https://oeis.org/A283713
Formalization: @longling12 (drafted with AI assistance)

Entry A283713 (Robert Price, Mar 17 2017), offset 0: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 758, based on the 5-celled von Neumann neighborhood. Initialized with a single black (ON) cell
at stage zero.
Conjectures from Colin Barker, Dec 10 2017:
G.f.: (1 + x - 9*x^2 + x^3 - 10*x^4 + 1000*x^6 - 1000*x^7 + 11000*x^8) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + x^2)).
a(n) = 10*a(n-1) + a(n-4) - 10*a(n-5) for n>4.

Modeling notes:
* Rule 758 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 758, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads (0, 0)..(n, 0) in base 10 from origin to right edge.
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z, which is equivalent since D(0) = 1.
-/

namespace OMA.S_oeis_a283713

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 758 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 758 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 758 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A283713(n): the cells (0, 0)..(n, 0) of stage n read in base 10 from origin to right edge. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) 0).toNat * 10 ^ (n - i)

/-- Barker's conjectures for A283713. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + X ^ 2)) =
      1 + X - 9 * X ^ 2 + X ^ 3 - 10 * X ^ 4 + 1000 * X ^ 6 - 1000 * X ^ 7 + 11000 * X ^ 8 ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 4) - 10 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a283713
