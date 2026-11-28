import Mathlib

/-!
# OEIS A283349: Barker's conjectures for the x-axis (left edge to origin, base 2) of Rule 617

Source: https://oeis.org/A283349
Formalization: @longling12 (drafted with AI assistance)

Entry A283349 (Robert Price, Mar 05 2017), offset 0: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 617, based on the 5-celled von Neumann neighborhood. Initialized with a single black (ON) cell
at stage zero.
Conjectures from Colin Barker, Mar 06 2017:
G.f.: (1 - x - x^2 + 2*x^3 + x^4 + 4*x^6) / ((1 - x)*(1 - 2*x)*(1 + 2*x)).
a(n) = (-16 + 3*(-2)^n + 5*2^n) / 8 for n>3.
a(n) = a(n-1) + 4*a(n-2) - 4*a(n-3) for n>4.

Modeling notes:
* Rule 617 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 617, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads (-n, 0)..(0, 0) in binary from left edge to origin.
* For n > 3, 8 divides -16 + 3*(-2)^n + 5*2^n, so integer division over Z is exact; the g.f. is stated in PowerSeries Z.
-/

namespace OMA.S_oeis_a283349

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 617 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 617 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 617 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A283349(n): the cells (-n, 0)..(0, 0) of stage n read in binary from left edge to origin. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) 0).toNat * 2 ^ (n - i)

/-- Barker's conjectures for A283349. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 - X - X ^ 2 + 2 * X ^ 3 + X ^ 4 + 4 * X ^ 6 ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = (-16 + 3 * (-2 : ℤ) ^ n + 5 * 2 ^ n) / 8) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a283349
