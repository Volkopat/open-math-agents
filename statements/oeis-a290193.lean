import Mathlib

/-!
# OEIS A290193: Corneth's and Wu's conjectures for the diagonal (origin to corner, base 10) of Rule 705

Source: https://oeis.org/A290193
Conjectures: David A. Corneth, Jul 23 2017; Chai Wah Wu, Nov 01 2018.
Formalization: @longling12 (drafted with AI assistance)

Entry A290193 (Robert Price, Jul 23 2017), offset 0: Binary representation of the diagonal from the
origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton defined
by Rule 705, based on the 5-celled von Neumann neighborhood. Initialized with a single black (ON)
cell at stage zero.
Conjecture (David A. Corneth, Jul 23 2017):
For even n > 3, binary representation of 3 * 2^(n - 1) - 1.
For odd n > 3, binary representation of 2^(n - 1) - 1.
From Chai Wah Wu, Nov 01 2018:
a(n) = a(n-1) + 100*a(n-2) - 100*a(n-3) for n > 5 (conjectured).
G.f.: (10000*x^5 - 10900*x^4 + 910*x^3 + 1)/((x - 1)*(10*x - 1)*(10*x + 1)) (conjectured).

Modeling notes:
* Rule 705 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 705, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* Following %N and the sequence data, a(n) reads the diagonal cells (0, 0), ..., (n, n) of the
  central (2n+1) x (2n+1) square as decimal digits with (0, 0) most significant and (n, n) least
  significant (the last line of %t in the OEIS entry extracts an x-axis row instead).
* toBinaryDecimal m = Nat.ofDigits 10 (Nat.digits 2 m) reads the binary digits of m in base 10.
  The denominator (x - 1)*(10*x - 1)*(10*x + 1) has constant term 1, so the generating function
  identity is stated as A(x) * D(x) = N(x) in PowerSeries Z.
-/

namespace OMA.S_oeis_a290193

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 705 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 705 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 705 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A290193(n): the diagonal cells (0, 0)..(n, n) of stage n read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) (i : ℤ)).toNat * 10 ^ (n - i)

/-- The base-2 digits of m read as a base-10 integer. -/
def toBinaryDecimal (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 2 m)

/-- Corneth's and Wu's conjectures for A290193. -/
theorem main :
    (∀ n : ℕ, 3 < n → n % 2 = 0 → a n = toBinaryDecimal (3 * 2 ^ (n - 1) - 1)) ∧
    (∀ n : ℕ, 3 < n → n % 2 = 1 → a n = toBinaryDecimal (2 ^ (n - 1) - 1)) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((X - 1) * (10 * X - 1) * (10 * X + 1)) =
      10000 * X ^ 5 - 10900 * X ^ 4 + 910 * X ^ 3 + 1 := by
  sorry

end OMA.S_oeis_a290193
