import Mathlib

/-!
# OEIS A282803: Barker's conjectures for the x-axis (origin to right edge, base 2) of Rule 507

Source: https://oeis.org/A282803
Formalization: @longling12 (drafted with AI assistance)

Entry A282803 (Robert Price, Feb 21 2017), offset 0: Decimal representation of the x-axis, from
the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 507, based on the 5-celled von Neumann neighborhood. Initialized with
a single black (ON) cell at stage zero.
From Colin Barker, Feb 22 2017, conjectures:
a(n) = 2^(n+1) - 1 for n>1 and even.
a(n) = (2^n - 2) / 3 for n>1 and odd.
a(n) = 5*a(n-2) - 4*a(n-4) for n>3.
G.f.: (1 + 2*x + 2*x^2 - 8*x^3 + 8*x^5) / ((1 - x)*(1 + x)*(1 - 2*x)*(1 + 2*x)).

Modeling notes:
* Rule 507 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 507, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads the cells (0, 0), (1, 0), ..., (n, 0) as binary digits with
  (0, 0) most significant and (n, 0) least significant, matching FromDigits[..., 2] in the
  entry's Mathematica program.
* For odd n, 3 divides 2^n - 2, so the integer division in the odd closed form is exact. The
  generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in PowerSeries Z,
  which is equivalent since D(0) = 1.
-/

namespace OMA.S_oeis_a282803

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 507 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 507 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 507 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A282803(n): the cells (0, 0)..(n, 0) of stage n read in binary from origin to right edge. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) 0).toNat * 2 ^ (n - i)

/-- Barker's closed forms, recurrence, and generating function conjectures for A282803. -/
theorem main :
    (∀ n : ℕ, 1 < n → n % 2 = 0 → (a n : ℤ) = 2 ^ (n + 1) - 1) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 1 → (a n : ℤ) = (2 ^ n - 2) / 3) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + 2 * X + 2 * X ^ 2 - 8 * X ^ 3 + 8 * X ^ 5 := by
  sorry

end OMA.S_oeis_a282803
