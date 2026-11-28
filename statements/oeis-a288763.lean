import Mathlib

/-!
# OEIS A288763: Barker's conjectures for the diagonal (origin to corner, base 2) of Rule 501

Source: https://oeis.org/A288763
Conjectures: Colin Barker, Jun 15 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A288763 (Robert Price, Jun 14 2017), offset 0: Decimal representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 501, based on the 5-celled von Neumann neighborhood. Initialized with a single
black (ON) cell at stage zero.
Conjectures from Colin Barker, Jun 15 2017:
G.f.: (1 + x - x^2 + 2*x^3 + 8*x^4 - 8*x^6 - 64*x^7 + 64*x^9) /
  ((1 - x)*(1 + x)*(1 - 2*x)*(1 + 2*x)).
a(n) = 3*2^(n - 1) for n>5 and even.
a(n) = 2^(n - 1) - 1 for n>5 and odd.
a(n) = 5*a(n-2) - 4*a(n-4) for n>4.

Modeling notes:
* Rule 501 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 501, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* Following %N and the sequence data, a(n) reads the diagonal cells (0, 0), ..., (n, n) of the
  central (2n+1) x (2n+1) square as binary digits with (0, 0) most significant and (n, n) least
  significant (the last line of %t in the OEIS entry extracts an x-axis row in base 10 instead).
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z since D(0) = 1; the recurrence is stated over Z.
-/

namespace OMA.S_oeis_a288763

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 501 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 501 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 501 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A288763(n): the diagonal cells (0, 0)..(n, n) of stage n read in binary. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) (i : ℤ)).toNat * 2 ^ (n - i)

/-- Barker's generating function, closed forms, and recurrence conjectures for A288763. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + X - X ^ 2 + 2 * X ^ 3 + 8 * X ^ 4 - 8 * X ^ 6 - 64 * X ^ 7 + 64 * X ^ 9 ∧
    (∀ n : ℕ, 5 < n → n % 2 = 0 → a n = 3 * 2 ^ (n - 1)) ∧
    (∀ n : ℕ, 5 < n → n % 2 = 1 → a n = 2 ^ (n - 1) - 1) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a288763
