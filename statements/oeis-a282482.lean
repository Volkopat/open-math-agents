import Mathlib

/-!
# OEIS A282482: Barker's conjectures for the x-axis (left edge to origin, base 10) of Rule 478

Source: https://oeis.org/A282482
Formalization: @longling12 (drafted with AI assistance)

Entry A282482 (Robert Price, Feb 16 2017), offset 0: Binary representation of the x-axis, from
the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 478, based on the 5-celled von Neumann neighborhood. Initialized with
a single black (ON) cell at stage zero.
Conjectures from Colin Barker, Feb 18 2017:
a(n) = a(n-2) + 10000*a(n-4) - 10000*a(n-6) for n>6.
G.f.: (1 + 11*x + 109*x^2 + 1100*x^3 + 890*x^4 - x^5 - 989*x^6 + 1000*x^10) /
  ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)*(1 + 100*x^2)).

Modeling notes:
* Rule 478 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 478, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads the cells (-n, 0), (-n+1, 0), ..., (0, 0) as digits in base 10 with
  (-n, 0) most significant and (0, 0) least significant, matching FromDigits[..., 10] in the
  entry's Mathematica program.
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z, which is equivalent since D(0) = 1.
-/

namespace OMA.S_oeis_a282482

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 478 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 478 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 478 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A282482(n): the cells (-n, 0)..(0, 0) of stage n read in base 10 from left edge to origin. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) 0).toNat * 10 ^ (n - i)

/-- Barker's recurrence and generating function conjectures for A282482. -/
theorem main :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = a (n - 2) + 10000 * a (n - 4) - 10000 * a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2)) =
      1 + 11 * X + 109 * X ^ 2 + 1100 * X ^ 3 + 890 * X ^ 4 - X ^ 5 - 989 * X ^ 6 +
      1000 * X ^ 10 := by
  sorry

end OMA.S_oeis_a282482
