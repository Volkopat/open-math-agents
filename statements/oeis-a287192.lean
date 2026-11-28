import Mathlib

/-!
# OEIS A287192: Barker's conjectures for the diagonal (corner to origin, base 2) of Rule 253

Source: https://oeis.org/A287192
Conjectures: Colin Barker, May 22 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A287192 (Robert Price, May 21 2017), offset 0: Decimal representation of the diagonal from
the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 253, based on the 5-celled von Neumann neighborhood. Initialized with a single
black (ON) cell at stage zero.
Conjectures from Colin Barker, May 22 2017:
G.f.: (1 + 2*x - 5*x^2 + 4*x^3 + 7*x^4 - 12*x^6) / ((1 - x)*(1 + x)*(1 - 2*x)*(1 + 2*x)).
a(n) = 3 for n>2 and even.
a(n) = 2*(2^n - 1) for n>2 and odd.
a(n) = 5*a(n-2) - 4*a(n-4) for n>4.

Modeling notes:
* Rule 253 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 253, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* Following %N and the sequence data, a(n) reads the diagonal cells (-n, -n), ..., (0, 0) of the
  central (2n+1) x (2n+1) square as binary digits with (-n, -n) most significant and (0, 0) least
  significant (the last line of %t in the OEIS entry extracts an x-axis row in base 10 instead).
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z since D(0) = 1; the recurrence is stated over Z.
-/

namespace OMA.S_oeis_a287192

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 253 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 253 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 253 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A287192(n): the diagonal cells (-n, -n)..(0, 0) of stage n read in binary. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) ((i : ℤ) - n)).toNat * 2 ^ (n - i)

/-- Barker's generating function, closed forms, and recurrence conjectures for A287192. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + 2 * X - 5 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 12 * X ^ 6 ∧
    (∀ n : ℕ, 2 < n → n % 2 = 0 → a n = 3) ∧
    (∀ n : ℕ, 2 < n → n % 2 = 1 → a n = 2 * (2 ^ n - 1)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a287192
