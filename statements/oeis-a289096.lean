import Mathlib

/-!
# OEIS A289096: Chai Wah Wu's conjectures for the diagonal (corner to origin, base 10) of Rule 545

Source: https://oeis.org/A289096
Conjectures: Chai Wah Wu, Nov 01 2018.
Formalization: @longling12 (drafted with AI assistance)

Entry A289096 (Robert Price, Jun 23 2017), offset 0: Binary representation of the diagonal from the
corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton defined
by Rule 545, based on the 5-celled von Neumann neighborhood. Initialized with a single black (ON)
cell at stage zero.
From Chai Wah Wu, Nov 01 2018:
a(n) = 10*a(n-1) + a(n-2) - 10*a(n-3) for n > 5 (conjectured).
G.f.: (100*x^5 - 10*x^4 + 10*x^2 + 1)/((x - 1)*(x + 1)*(10*x - 1)) (conjectured).

Modeling notes:
* Rule 545 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 545, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* Following %N and the sequence data, a(n) reads the diagonal cells (-n, -n), ..., (0, 0) of the
  central (2n+1) x (2n+1) square as decimal digits with (-n, -n) most significant and (0, 0) least
  significant (the last line of %t in the OEIS entry extracts an x-axis row instead).
* The denominator (x - 1)*(x + 1)*(10*x - 1) has constant term (-1)*1*(-1) = 1, a unit in Z, so the
  generating function identity is stated as A(x) * D(x) = N(x) in PowerSeries Z.
-/

namespace OMA.S_oeis_a289096

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 545 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 545 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 545 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A289096(n): the diagonal cells (-n, -n)..(0, 0) of stage n read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) ((i : ℤ) - n)).toNat * 10 ^ (n - i)

/-- Chai Wah Wu's recurrence and generating function conjectures for A289096. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((X - 1) * (X + 1) * (10 * X - 1)) =
      100 * X ^ 5 - 10 * X ^ 4 + 10 * X ^ 2 + 1 := by
  sorry

end OMA.S_oeis_a289096
