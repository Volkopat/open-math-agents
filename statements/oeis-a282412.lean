import Mathlib

/-!
# OEIS A282412: Barker's conjectures for the x-axis (origin to right edge, base 10) of Rule 467

Source: https://oeis.org/A282412
Formalization: @longling12 (drafted with AI assistance)

Entry A282412 (Robert Price, Feb 14 2017), offset 0: Binary representation of the x-axis, from
the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 467, based on the 5-celled von Neumann neighborhood. Initialized with
a single black (ON) cell at stage zero.
Conjectures from Colin Barker, Feb 15 2017:
a(n) = (1 + (-1)^n)*(10^(1+n)-1) / 18 for n>1.
a(n) = 101*a(n-2) - 100*a(n-4) for n>3.
G.f.: (1+10*x+10*x^2-1010*x^3+1000*x^5) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)).

Modeling notes:
* Rule 467 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 467, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads the cells (0, 0), (1, 0), ..., (n, 0) as digits in base 10 with
  (0, 0) most significant and (n, 0) least significant, matching FromDigits[..., 10] in the
  entry's Mathematica program.
* Since 2 divides 1 + (-1)^n and 9 divides 10^(1+n) - 1 for every n, integer division by 18 over
  Z is exact. The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x)
  in PowerSeries Z.
-/

namespace OMA.S_oeis_a282412

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 467 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 467 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 467 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A282412(n): the cells (0, 0)..(n, 0) of stage n read in base 10 from origin to right edge. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) 0).toNat * 10 ^ (n - i)

/-- Barker's closed-form, recurrence, and generating function conjectures for A282412. -/
theorem main :
    (∀ n : ℕ, 1 < n → (a n : ℤ) = (1 + (-1 : ℤ) ^ n) * (10 ^ (1 + n) - 1) / 18) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      1 + 10 * X + 10 * X ^ 2 - 1010 * X ^ 3 + 1000 * X ^ 5 := by
  sorry

end OMA.S_oeis_a282412
