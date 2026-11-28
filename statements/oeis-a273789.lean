import Mathlib

/-!
# A273789: Number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by "Rule 931", based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A273789
Credit: @Salofe

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.

The conjectures, quoted verbatim from the FORMULA section of the entry:

  Conjectures from _Colin Barker_, May 31 2016: (Start)
  a(n) = (1+2*n)^2 = A273743(n) = A016754(n) for n>1.
  a(n) = 3*a(n-1)-3*a(n-2)+a(n-3) for n>4.
  G.f.: (1+2*x+13*x^2-12*x^3+4*x^4) / (1-x)^3.
  (End)

Formalization notes:
* Offset 0 (comment of the entry: "Initialized with a single black (ON) cell at stage zero"):
  stage 0 is a single ON cell at the origin of the infinite grid ℤ × ℤ, every other cell OFF,
  and stage n+1 is obtained from stage n by one synchronous update of every cell, the infinite
  background included.
* Rule 931 is read in Wolfram's numbering of the 5-neighbour outer totalistic rules, as in the
  entry's Mathematica program (rule = IntegerDigits[931,2,10], rule[[10-#]] applied to
  ListConvolve with kernel {{0,2,0},{2,1,2},{0,2,0}}): a cell whose own value is c (0 or 1)
  and which has k ON cells among its four orthogonal neighbours becomes bit c + 2*k of 931
  (bit 0 is the least significant one; 931 = 1110100011 in binary). Below, `rule code` is this
  rule for an arbitrary code and `state code n` is stage n of the automaton with that code.
* As in the published Mathematica program (stage n is trimmed to the (2n+1) × (2n+1) square
  centred on the initial cell, Part[..., Range[k+1-n, k-1+n]], before the cell values are
  added up), a(n) is the number of ON cells (x, y) with -n ≤ x ≤ n and -n ≤ y ≤ n at stage n.
  The program evolves a finite cyclic grid of side 2*128+1; on these squares it agrees with the
  infinite grid used here for every n ≤ 128 (a cell of the square at stage n depends only on
  the cells within distance n of it at stage 0, and none of these wraps around). This
  convention reproduces all 129 terms of the b-file (n = 0..128).
* A273743 is the sequence of the same construction for Rule 901 (OEIS A273743, offset 0, same
  program with code=901); it is defined below by the same counting with code 901. A016754 is
  the sequence of odd squares (OEIS name: Odd squares: a(n) = (2n+1)^2; offset 0), defined
  below by that formula.
* First conjunct: the chain a(n) = (1+2n)^2 = A273743(n) = A016754(n) for n > 1, exactly the
  range of the conjecture, as the conjunction of its three consecutive equalities, read in ℕ
  (none of them involves a subtraction).
* Second conjunct: the recurrence for n > 4, exactly the range of the conjecture; there n - 1,
  n - 2 and n - 3 are exact natural-number subtractions, and the identity is read in ℤ.
* Third conjunct: the generating function, written as the product identity
  A(x) * (1-x)^3 = 1+2x+13x^2-12x^3+4x^4 in ℤ⟦X⟧, where A(x) = Σ a(n) x^n. The factor (1-x)^3
  has constant coefficient 1, hence is invertible in ℤ⟦X⟧, so the identity is equivalent to
  the quotient form of the conjecture and needs no division.
-/

namespace OMA.S_oeis_a273789

/-- A configuration of the plane: `g x y` is the value of the cell `(x, y)` (true = ON). -/
abbrev Grid := ℤ → ℤ → Bool

/-- The value of a cell as a number: 1 for ON, 0 for OFF. -/
def bit (b : Bool) : ℕ := if b then 1 else 0

/-- The 5-neighbour outer totalistic rule with code `code`: a cell with own value `c` and `k`
ON orthogonal neighbours becomes bit `bit c + 2 * k` of `code` (bit 0 = least significant). -/
def rule (code : ℕ) (c : Bool) (k : ℕ) : Bool :=
  decide ((code / 2 ^ (bit c + 2 * k)) % 2 = 1)

/-- The number of ON cells among the four orthogonal neighbours of `(x, y)`. -/
def neighbors (g : Grid) (x y : ℤ) : ℕ :=
  bit (g (x + 1) y) + bit (g (x - 1) y) + bit (g x (y + 1)) + bit (g x (y - 1))

/-- One synchronous update of the whole plane by the rule with code `code`. -/
def step (code : ℕ) (g : Grid) : Grid := fun x y => rule code (g x y) (neighbors g x y)

/-- A single ON cell at the origin, every other cell OFF. -/
def initial : Grid := fun x y => decide (x = 0 ∧ y = 0)

/-- The configuration at stage `n` of the automaton with code `code`. -/
def state (code : ℕ) : ℕ → Grid
  | 0 => initial
  | n + 1 => step code (state code n)

/-- The number of ON cells `(x, y)` with `-n ≤ x ≤ n` and `-n ≤ y ≤ n` at stage `n` of the
automaton with code `code`: the pair `(i, j)` with `0 ≤ i, j ≤ 2n` stands for the cell
`(x, y) = (i - n, j - n)`. -/
def onCount (code n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Fin (2 * n + 1) × Fin (2 * n + 1) =>
    state code n (((p.1 : ℕ) : ℤ) - n) (((p.2 : ℕ) : ℤ) - n) = true)).card

/-- A273789: the number of ON cells at stage `n` of Rule 931. -/
def a (n : ℕ) : ℕ := onCount 931 n

/-- A273743: the number of ON cells at stage `n` of Rule 901 (the same construction). -/
def A273743 (n : ℕ) : ℕ := onCount 901 n

/-- A016754, the odd squares: A016754(n) = (2n+1)^2, offset 0. -/
def A016754 (n : ℕ) : ℕ := (2 * n + 1) ^ 2

theorem main :
    (∀ n : ℕ, 1 < n →
      a n = (1 + 2 * n) ^ 2 ∧ (1 + 2 * n) ^ 2 = A273743 n ∧ A273743 n = A016754 n) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 =
      1 + 2 * PowerSeries.X + 13 * PowerSeries.X ^ 2 - 12 * PowerSeries.X ^ 3
        + 4 * PowerSeries.X ^ 4) := by sorry

end OMA.S_oeis_a273789
