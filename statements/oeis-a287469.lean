import Mathlib

/-!
# OEIS A287469: Barker's conjectures for the diagonal (origin to corner, base 10) of Rule 276

Source: https://oeis.org/A287469
Conjectures: Colin Barker, May 29 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A287469 (Robert Price, May 26 2017), offset 0: Binary representation of the diagonal from the
origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton defined
by Rule 276, based on the 5-celled von Neumann neighborhood. Initialized with a single black (ON)
cell at stage zero.
From Colin Barker, May 29 2017:
Conjectures:
G.f.: 1 / ((1 - 10*x)*(1 + 10*x)*(1 - 10*x^2)).
a(n) = (10^(n+1) - 10^(n/2)) / 9 for n even.
a(n) = 0 for n odd.
a(n) = 110*a(n-2) - 1000*a(n-4) for n>3.

Modeling notes:
* Rule 276 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 276, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* Following %N and the sequence data, a(n) reads the diagonal cells (0, 0), ..., (n, n) of the
  central (2n+1) x (2n+1) square as decimal digits with (0, 0) most significant and (n, n) least
  significant (the last line of %t in the OEIS entry extracts an x-axis row instead).
* For even n = 2m, 10^(2m+1) - 10^m = 10^m * (10^(m+1) - 1) is divisible by 9, so integer division
  by 9 and n / 2 are exact. The generating function identity is stated as A(x) * D(x) = 1 in
  PowerSeries Z since D(0) = 1.
-/

namespace OMA.S_oeis_a287469

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 276 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 276 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 276 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A287469(n): the diagonal cells (0, 0)..(n, n) of stage n read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) (i : ℤ)).toNat * 10 ^ (n - i)

/-- Barker's generating function, closed forms, and recurrence conjectures for A287469. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) = 1 ∧
    (∀ n : ℕ, n % 2 = 0 → (a n : ℤ) = (10 ^ (n + 1) - 10 ^ (n / 2)) / 9) ∧
    (∀ n : ℕ, n % 2 = 1 → a n = 0) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 110 * a (n - 2) - 1000 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a287469
