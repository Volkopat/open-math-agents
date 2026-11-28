import Mathlib

/-!
# OEIS A284179: Barker's conjectures for the x-axis (left edge to origin, base 10) of Rule 813

Source: https://oeis.org/A284179
Formalization: @longling12 (drafted with AI assistance)

Entry A284179 (Robert Price, Mar 21 2017), offset 0: Binary representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 813, based on the 5-celled von Neumann neighborhood. Initialized with a single black (ON) cell
at stage zero.
Conjectures from Colin Barker, Mar 22 2017:
G.f.: (1 + 9*x + 91*x^2 + 909*x^3 - 899*x^4 + 1000*x^5 - 1000*x^6 + 900*x^7 + 90*x^8 + 9*x^9 + x^10 + 10000*x^13 - 10000*x^14) / ((1 - x)*(1 - 10*x)*(1 + 10*x)*(1 + 100*x^2)).
a(n) = a(n-1) + 10000*a(n-4) - 10000*a(n-5) for n>10.

Modeling notes:
* Rule 813 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 813, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads (-n, 0)..(0, 0) in base 10 from left edge to origin.
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z, which is equivalent since D(0) = 1.
-/

namespace OMA.S_oeis_a284179

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 813 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 813 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 813 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A284179(n): the cells (-n, 0)..(0, 0) of stage n read in base 10 from left edge to origin. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) 0).toNat * 10 ^ (n - i)

/-- Barker's conjectures for A284179. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2)) =
      1 + 9 * X + 91 * X ^ 2 + 909 * X ^ 3 - 899 * X ^ 4 + 1000 * X ^ 5 - 1000 * X ^ 6 +
      900 * X ^ 7 + 90 * X ^ 8 + 9 * X ^ 9 + X ^ 10 + 10000 * X ^ 13 - 10000 * X ^ 14 ∧
    (∀ n : ℕ, 10 < n → (a n : ℤ) = a (n - 1) + 10000 * a (n - 4) - 10000 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a284179
