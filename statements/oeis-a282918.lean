import Mathlib

/-!
# OEIS A282918: Barker's conjectures for the x-axis (origin to right edge, base 2) of Rule 529

Source: https://oeis.org/A282918
Formalization: @longling12 (drafted with AI assistance)

Entry A282918 (Robert Price, Feb 24 2017), offset 0: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 529, based on the 5-celled von Neumann neighborhood. Initialized with a single black (ON) cell
at stage zero.
Conjectures from Colin Barker, Feb 25 2017:
a(n) = 4*a(n-2) + a(n-4) - 4*a(n-6) for n>6.
G.f.: (1 + 11*x^4 + 32*x^5 - 84*x^6 - 128*x^10) / ((1 - x)*(1 + x)*(1 - 2*x)*(1 + 2*x)*(1 + x^2)).

Modeling notes:
* Rule 529 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 529, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads (0, 0)..(n, 0) in binary from origin to right edge.
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in PowerSeries Z.
-/

namespace OMA.S_oeis_a282918

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 529 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 529 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 529 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A282918(n): the cells (0, 0)..(n, 0) of stage n read in binary from origin to right edge. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) 0).toNat * 2 ^ (n - i)

/-- Barker's conjectures for A282918. -/
theorem main :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 4 * a (n - 2) + a (n - 4) - 4 * a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + X ^ 2)) =
      1 + 11 * X ^ 4 + 32 * X ^ 5 - 84 * X ^ 6 - 128 * X ^ 10 := by
  sorry

end OMA.S_oeis_a282918
