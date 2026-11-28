import Mathlib

/-!
# OEIS A289404: Barker's and Provvedi's conjectures for the diagonal of Rule 566

Source: https://oeis.org/A289404
Conjectures: Colin Barker, Jul 05 2017; Federico Provvedi, Nov 21 2018.
Formalization: @longling12 (drafted with AI assistance)

Entry A289404 (Robert Price, Jul 05 2017), offset 0: Binary representation of the diagonal from the
corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton defined
by Rule 566, based on the 5-celled von Neumann neighborhood. Initialized with a single black (ON)
cell at stage zero.
Conjectures from Colin Barker, Jul 05 2017:
G.f.: 1 / ((1 - x)*(1 - 10*x^2)).
a(n) = a(n-1) + 10*a(n-2) - 10*a(n-3) for n>2.
Conjectures from Federico Provvedi, Nov 21 2018:
a(n) = (10^(1 + floor(n/2)) - 1)/9.
a(n) = (sqrt(10)^(n+1)*((sqrt(10)-1)*(-1)^n+(sqrt(10)+1))-2)/18.

Modeling notes:
* Rule 566 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 566, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* Matching %N and %t (Table[ca[[i, j, j]], {j, 1, i}] with FromDigits base 10), a(n) reads the
  diagonal cells (-n, -n), ..., (0, 0) as decimal digits with (-n, -n) most significant.
* The generating function is stated as A(x) * D(x) = 1 in PowerSeries Z since D(0) = 1; the
  recurrence is stated over Z; Provvedi's floor formula uses Int.floor on Q, and his radical
  formula uses Real.sqrt over R.
-/

namespace OMA.S_oeis_a289404

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 566 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 566 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 566 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A289404(n): the diagonal cells (-n, -n)..(0, 0) of stage n read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) ((i : ℤ) - n)).toNat * 10 ^ (n - i)

/-- Barker's and Provvedi's conjectures for A289404. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 10 * X ^ 2)) = 1 ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = a (n - 1) + 10 * a (n - 2) - 10 * a (n - 3)) ∧
    (∀ n : ℕ, (a n : ℚ) = ((10 : ℚ) ^ (1 + ⌊(n : ℚ) / 2⌋) - 1) / 9) ∧
    (∀ n : ℕ, (a n : ℝ) =
      (Real.sqrt 10 ^ (n + 1) * ((Real.sqrt 10 - 1) * (-1) ^ n + (Real.sqrt 10 + 1)) - 2) / 18) := by
  sorry

end OMA.S_oeis_a289404
