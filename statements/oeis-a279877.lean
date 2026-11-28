import Mathlib

/-!
# OEIS A279877: Barker's conjectures for the x-axis (left edge to origin, base 10) of Rule 213

Source: https://oeis.org/A279877
Conjectures: Colin Barker, Dec 21 2016.
Formalization: @longling12 (drafted with AI assistance)

Entry A279877 (Robert Price, Dec 20 2016), offset 0: Binary representation of the x-axis, from the
left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 213, based on the 5-celled von Neumann neighborhood. Initialized with a single
black (ON) cell at stage zero.
Conjectures from Colin Barker, Dec 21 2016:
a(n) = 111*a(n-2)-1110*a(n-4)+1000*a(n-6) for n>6.
G.f.: (1 +10*x -101*x^2 -10*x^3 +111*x^4 -1110*x^6 +1000*x^8) /
  ((1 -x)*(1 +x)*(1 -10*x)*(1 +10*x)*(1 -10*x^2)).

Modeling notes:
* Rule 213 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 213, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads the x-axis cells (-n, 0), (-n + 1, 0), ..., (0, 0) as decimal digits with
  (-n, 0) most significant and (0, 0) least significant, matching %t (FromDigits base 10).
* The recurrence is stated over Z, and the generating function identity A(x) = N(x)/D(x) is stated
  as A(x) * D(x) = N(x) in PowerSeries Z since D(0) = 1.
-/

namespace OMA.S_oeis_a279877

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 213 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 213 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 213 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A279877(n): the x-axis cells (-n, 0)..(0, 0) of stage n read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) 0).toNat * 10 ^ (n - i)

/-- Barker's recurrence and generating function conjectures for A279877. -/
theorem main :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 111 * a (n - 2) - 1110 * a (n - 4) + 1000 * a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      1 + 10 * X - 101 * X ^ 2 - 10 * X ^ 3 + 111 * X ^ 4 - 1110 * X ^ 6 + 1000 * X ^ 8 := by
  sorry

end OMA.S_oeis_a279877
