import Mathlib

/-!
# OEIS A285540: Barker's conjectures for the diagonal (corner to origin, base 10) of Rule 35

Source: https://oeis.org/A285540
Formalization: @longling12 (drafted with AI assistance)

Entry A285540 (Robert Price, Apr 20 2017), offset 0: Binary representation of the diagonal from
the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 35, based on the 5-celled von Neumann neighborhood. Initialized with a single
black (ON) cell at stage zero.
Conjectures from Colin Barker, Apr 21 2017:
G.f.: (1 + 10*x - 110*x^2) / ((1 - x)*(1 - 10*x)*(1 + 10*x)*(1 - 10*x^2)).
a(n) = (-1 - (-2)^n*5^(1+n) + 2^n*5^(1+n) + 2^(n/2)*5^(1+n/2)*(1+(-1)^n)) / 9.

Modeling notes:
* Rule 35 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 35, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads the diagonal cells (-n, -n), (-n+1, -n+1), ..., (0, 0) of the central
  (2n+1) x (2n+1) square in base 10 with (-n, -n) most significant and (0, 0) least significant,
  as specified by the entry's definition and data (note that Price's %t line in the OEIS entry
  extracts the x-axis rather than the diagonal).
* In the closed form, the factor (1 + (-1)^n) vanishes for odd n and n / 2 is exact for even n;
  moreover 9 divides the numerator for every n, so the integer division over Z is exact. The
  generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in PowerSeries Z.
-/

namespace OMA.S_oeis_a285540

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 35 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 35 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 35 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A285540(n): the diagonal cells (-n, -n)..(0, 0) of stage n read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) ((i : ℤ) - n)).toNat * 10 ^ (n - i)

/-- Barker's generating function and closed-form conjectures for A285540. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      1 + 10 * X - 110 * X ^ 2 ∧
    (∀ n : ℕ, (a n : ℤ) =
      (-1 - (-2 : ℤ) ^ n * 5 ^ (1 + n) + 2 ^ n * 5 ^ (1 + n) +
        2 ^ (n / 2) * 5 ^ (1 + n / 2) * (1 + (-1) ^ n)) / 9) := by
  sorry

end OMA.S_oeis_a285540
