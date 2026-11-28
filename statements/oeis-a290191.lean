import Mathlib

/-!
# OEIS A290191: Conjecture for the diagonal (corner to origin, base 10) of Rule 673

Source: https://oeis.org/A290191
Formalization: @longling12 (drafted with AI assistance)

Entry A290191 (Robert Price, Jul 23 2017), offset 0: Binary representation of the diagonal from the
corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton defined
by Rule 673, based on the 5-celled von Neumann neighborhood. Initialized with a single black (ON)
cell at stage zero.
Formula section:
Conjecture: a(n) is the binary representation of 2^(n - 1) - 1 - (n mod 2).

Modeling notes:
* Rule 673 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 673, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* Following %N and the sequence data, a(n) reads the diagonal cells (-n, -n), ..., (0, 0) of the
  central (2n+1) x (2n+1) square as decimal digits with (-n, -n) most significant and (0, 0) least
  significant (the last line of %t in the OEIS entry extracts an x-axis row instead).
* For m : N, toBinaryDecimal m = Nat.ofDigits 10 (Nat.digits 2 m) interprets the base-2 digits of m
  as decimal digits. To avoid N-truncation at n = 0, 1, the expression 2^(n - 1) - 1 - (n mod 2) is
  evaluated in Q and equated to (m : Q).
-/

namespace OMA.S_oeis_a290191

/-- One step of the two-dimensional outer totalistic Rule 673 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 673 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 673 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A290191(n): the diagonal cells (-n, -n)..(0, 0) of stage n read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) ((i : ℤ) - n)).toNat * 10 ^ (n - i)

/-- The base-2 digits of m read as a base-10 integer. -/
def toBinaryDecimal (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 2 m)

/-- The conjecture from the OEIS entry for A290191. -/
theorem main :
    ∀ n : ℕ, ∃ m : ℕ,
      (m : ℚ) = (2 : ℚ) ^ ((n : ℤ) - 1) - 1 - ((n % 2 : ℕ) : ℚ) ∧
      a n = toBinaryDecimal m := by
  sorry

end OMA.S_oeis_a290191
