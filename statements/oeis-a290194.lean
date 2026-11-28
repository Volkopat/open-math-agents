import Mathlib

/-!
# OEIS A290194: Corneth's and Wu's conjectures for the diagonal (corner to origin, base 2) of Rule 705

Source: https://oeis.org/A290194
Conjectures: David A. Corneth, Jul 23 2017; Chai Wah Wu, Nov 01 2018.
Formalization: @longling12 (drafted with AI assistance)

Entry A290194 (Robert Price, Jul 23 2017), offset 0: Decimal representation of the diagonal from
the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 705, based on the 5-celled von Neumann neighborhood. Initialized with a single
black (ON) cell at stage zero.
Conjecture (David A. Corneth, Jul 23 2017):
a(n) = Fibonacci(2*n+1) if n <= 3, for n > 3, a(n) = 2*a(n-1) + 2 if n is even,
a(n) = 2*a(n-1) + 5 if n is odd. It would follow that a(n) = 2^(n+1) - 4 + (n mod 2) for n >= 3.
From Chai Wah Wu, Nov 01 2018:
a(n) = 2*a(n-1) + a(n-2) - 2*a(n-3) for n > 5 (conjectured).
G.f.: (2*x^5 + x^4 + 3*x^3 + 1)/((x - 1)*(x + 1)*(2*x - 1)) (conjectured).

Modeling notes:
* Rule 705 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 705, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* Following %N and the sequence data, a(n) reads the diagonal cells (-n, -n), ..., (0, 0) of the
  central (2n+1) x (2n+1) square as binary digits with (-n, -n) most significant and (0, 0) least
  significant (the last line of %t in the OEIS entry extracts an x-axis row in base 10 instead).
* Fibonacci(2*n + 1) is Mathlib's Nat.fib (2 * n + 1). The denominator (x - 1)*(x + 1)*(2*x - 1)
  has constant term 1, so the generating function identity is stated as A(x) * D(x) = N(x) in
  PowerSeries Z.
-/

namespace OMA.S_oeis_a290194

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 705 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 705 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 705 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A290194(n): the diagonal cells (-n, -n)..(0, 0) of stage n read in binary. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) ((i : ℤ) - n)).toNat * 2 ^ (n - i)

/-- Corneth's and Wu's conjectures for A290194. -/
theorem main :
    (∀ n : ℕ, n ≤ 3 → a n = Nat.fib (2 * n + 1)) ∧
    (∀ n : ℕ, 3 < n → n % 2 = 0 → a n = 2 * a (n - 1) + 2) ∧
    (∀ n : ℕ, 3 < n → n % 2 = 1 → a n = 2 * a (n - 1) + 5) ∧
    (∀ n : ℕ, 3 ≤ n → a n = 2 ^ (n + 1) - 4 + n % 2) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((X - 1) * (X + 1) * (2 * X - 1)) =
      2 * X ^ 5 + X ^ 4 + 3 * X ^ 3 + 1 := by
  sorry

end OMA.S_oeis_a290194
