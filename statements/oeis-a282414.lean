import Mathlib

/-!
# OEIS A282414: Barker's and Mathar's conjectures for the x-axis (origin to right edge, base 2) of Rule 467

Source: https://oeis.org/A282414
Formalization: @longling12 (drafted with AI assistance)

Entry A282414 (Robert Price, Feb 14 2017), offset 0: Decimal representation of the x-axis, from
the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 467, based on the 5-celled von Neumann neighborhood. Initialized with
a single black (ON) cell at stage zero.
Conjectures from Colin Barker, Feb 15 2017:
a(n) = 2^(n+1)-1 for n>1 and even.
a(n) = 0 for n>1 and odd.
a(n) = 5*a(n-2) - 4*a(n-4) for n>3.
G.f.: (1 + 2*x + 2*x^2 - 10*x^3 + 8*x^5) / ((1 - x)*(1 + x)*(1 - 2*x)*(1 + 2*x)).
Equivalent conjecture (R. J. Mathar, Jun 21 2025): a(n) = A282413(n) for n>=2.

Modeling notes:
* Rule 467 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 467, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads (0, 0)..(n, 0) in binary from origin to right edge, while a282413(n)
  (entry A282413, offset 0) reads (-n, 0)..(0, 0) in binary from left edge to origin.
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z, which is equivalent since D(0) = 1.
-/

namespace OMA.S_oeis_a282414

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 467 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 467 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 467 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A282414(n): the cells (0, 0)..(n, 0) of stage n read in binary from origin to right edge. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) 0).toNat * 2 ^ (n - i)

/-- A282413(n): the cells (-n, 0)..(0, 0) of stage n read in binary from left edge to origin. -/
def a282413 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) 0).toNat * 2 ^ (n - i)

/-- Barker's and Mathar's conjectures for A282414. -/
theorem main :
    (∀ n : ℕ, 1 < n → n % 2 = 0 → (a n : ℤ) = 2 ^ (n + 1) - 1) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 1 → a n = 0) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + 2 * X + 2 * X ^ 2 - 10 * X ^ 3 + 8 * X ^ 5 ∧
    (∀ n : ℕ, 2 ≤ n → a n = a282413 n) := by
  sorry

end OMA.S_oeis_a282414
