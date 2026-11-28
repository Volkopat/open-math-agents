import Mathlib

/-!
# A173524: a(n) = A053737(4^k+n-1) in the limit k->infinity, where k plays the role of a row index in A053737.

Source: https://oeis.org/A173524
Credit: @agchua

Comment and formula lines of A173524 (the entry is by Omar E. Pol, Feb 20 2010), verbatim:
  It appears that if A053737 is written as a triangle then the rows are initial segments of the
  present sequence; see the conjecture in A000120.
  Conjecture: Fixed point of the morphism 1->{1,2,3,...,b}, 2->{2,3,4,...,b+1},
  j->{j,j+1,...,j+b-1} for b=4. [Joerg Arndt, Dec 08 2010]
Offset of A173524: 1 (data 1, 2, 3, 4, 2, 3, 4, 5, 3, ...). A053737(m) is the sum of the
base-4 digits of m (offset 0), with A053737(0) = 0.

Definition. The name defines a(n) as the limit of A053737(4^k + n - 1) for k -> infinity. The
formula line of R. J. Mathar, a(n) = A053737(4^k+n-1) where k >= ceiling(log_4(n/3)), says that
this value does not change from k = ceiling(log_4(n/3)) on; k = n is such a value, and the Lean
function below takes k = n. The first part of the statement says that this is the limit, so the
function is the sequence of the name line.

Formalisation of the two conjectures.
(1) The entry A053737 displays itself as the triangle 0, / 1,2,3, / 1,2,3,4,2,3,4,5,3,4,5,6, / ...
    with row 0 = A053737(0) and, for k >= 0, row k+1 = A053737(4^k), ..., A053737(4^(k+1) - 1),
    a row of length 3*4^k. Row k+1 is an initial segment of the present sequence means:
    A053737(4^k + j) = a(j+1) for 0 <= j < 3*4^k. Row 0 (the single entry 0, while a(1) = 1)
    is left out: it is the zero row of the display, and the claim is about the rows from row 1 on.
(2) For b = 4 the morphism maps the letter j to the word j, j+1, j+2, j+3, so the image of a
    sequence u(1), u(2), ... has the term u(i+1) + j at position 4*i + j + 1 (i >= 0,
    0 <= j <= 3). A fixed point is a sequence equal to its own image; the one meant here starts
    with the letter 1 (as in the data). So the conjecture says: a(1) = 1 and
    a(4*i + j + 1) = a(i + 1) + j for all i >= 0 and 0 <= j <= 3.
-/

namespace OMA.S_oeis_a173524

/-- A053737(m): the sum of the digits of m written in base 4. -/
def A053737 (m : ℕ) : ℕ := (Nat.digits 4 m).sum

/-- A173524(n), n >= 1: the value A053737(4^k + n - 1) at k = n (see above). -/
def a (n : ℕ) : ℕ := A053737 (4 ^ n + n - 1)

/-- Entry j of row k+1 of the triangle of A053737 (0 <= j < 3*4^k). -/
def rowEntry (k j : ℕ) : ℕ := A053737 (4 ^ k + j)

/-- a(n) is the limit of A053737(4^k + n - 1); the rows of the triangle of A053737 (from row 1
on) are initial segments of a; and a is the fixed point, starting with 1, of the morphism
j -> j, j+1, j+2, j+3. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → A053737 (4 ^ k + n - 1) = a n) ∧
    (∀ k j : ℕ, j < 3 * 4 ^ k → rowEntry k j = a (j + 1)) ∧
    (a 1 = 1 ∧ ∀ i j : ℕ, j < 4 → a (4 * i + j + 1) = a (i + 1) + j) := by
  sorry

end OMA.S_oeis_a173524
