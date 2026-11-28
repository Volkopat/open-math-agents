import Mathlib

/-!
# A273743: Number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by "Rule 901", based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A273743
Credit: @Salofe

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.

The conjectures, quoted verbatim from the FORMULA section of the entry:

  Conjectures from _Colin Barker_, May 29 2016: (Start)
  a(n) = (1+2*n)^2 = A016754(n) for n>1.
  a(n) = 3*a(n-1)-3*a(n-2)+a(n-3) for n>4.
  G.f.: (1+5*x+4*x^2-3*x^3+x^4) / (1-x)^3.
  (End)

Formalization notes:
* Offset 0 (comment of the entry: "Initialized with a single black (ON) cell at stage zero"):
  stage 0 is a single ON cell at the origin of the infinite grid ℤ × ℤ, every other cell OFF,
  and stage n+1 is obtained from stage n by one synchronous update of every cell, the infinite
  background included.
* Rule 901 is read in Wolfram's numbering of the 5-neighbour outer totalistic rules, as in the
  entry's Mathematica program (rule = IntegerDigits[901,2,10], rule[[10-#]] applied to
  ListConvolve with kernel {{0,2,0},{2,1,2},{0,2,0}}): a cell whose own value is c (0 or 1)
  and which has k ON cells among its four orthogonal neighbours becomes bit c + 2*k of 901
  (bit 0 is the least significant one; 901 = 1110000101 in binary). Bit 0 of 901 is 1, so the
  OFF background turns ON at stage 1.
* As in the published Mathematica program (stage n is trimmed to the (2n+1) × (2n+1) square
  centred on the initial cell, Part[..., Range[k+1-n, k-1+n]], before the cell values are
  added up), a(n) is the number of ON cells (x, y) with -n ≤ x ≤ n and -n ≤ y ≤ n at stage n.
  The program evolves a finite cyclic grid of side 2*128+1; on these squares it agrees with the
  infinite grid used here. This convention reproduces all 129 terms of the b-file
  (n = 0..128).
* First conjunct: the closed form for n > 1, exactly the range of the conjecture, read in ℕ
  (it involves no subtraction), together with the cross-reference a(n) = A016754(n). A016754
  is the sequence of odd squares (OEIS name: "Odd squares: a(n) = (2n+1)^2", offset 0), and it
  is defined below by that formula.
* Second conjunct: the recurrence for n > 4, exactly the range of the conjecture; there n - 1,
  n - 2 and n - 3 are exact natural-number subtractions, and the identity is read in ℤ.
* Third conjunct: the generating function, written as the product identity
  A(x) * (1-x)^3 = 1+5x+4x^2-3x^3+x^4 in ℤ⟦X⟧, where A(x) = Σ a(n) x^n. The factor (1-x)^3
  has constant coefficient 1, hence is invertible in ℤ⟦X⟧, so the identity is equivalent to
  the quotient form of the conjecture and needs no division.
-/
namespace OMA.S_oeis_a273743

/-- A configuration of the plane: `g x y` is the value of the cell `(x, y)` (true = ON). -/
abbrev Grid := ℤ → ℤ → Bool

/-- The value of a cell as a number: 1 for ON, 0 for OFF. -/
def bit (b : Bool) : ℕ := if b then 1 else 0

/-- Rule 901: a cell with own value `c` and `k` ON orthogonal neighbours becomes
bit `bit c + 2 * k` of 901. -/
def rule (c : Bool) (k : ℕ) : Bool :=
  decide ((901 / 2 ^ (bit c + 2 * k)) % 2 = 1)

/-- The number of ON cells among the four orthogonal neighbours of `(x, y)`. -/
def neighbors (g : Grid) (x y : ℤ) : ℕ :=
  bit (g (x+1) y) + bit (g (x-1) y) + bit (g x (y+1)) + bit (g x (y-1))

/-- One synchronous update of the whole plane. -/
def step (g : Grid) : Grid := fun x y => rule (g x y) (neighbors g x y)

/-- A single ON cell at the origin, every other cell OFF. -/
def initial : Grid := fun x y => decide (x = 0 ∧ y = 0)

/-- The configuration at stage n. -/
def state : ℕ → Grid
  | 0 => initial
  | n+1 => step (state n)

/-- The number of ON cells `(x, y)` with `-n ≤ x ≤ n` and `-n ≤ y ≤ n` at stage n: the sum of
the cell values over that square, where `i` and `j` run over `0 .. 2n` and stand for
`x = i - n` and `y = j - n`. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2*n+1), ∑ j ∈ Finset.range (2*n+1),
    bit (state n ((i:ℤ) - n) ((j:ℤ) - n))

/-- A016754, the odd squares: A016754(n) = (2n+1)^2, offset 0. -/
def A016754 (n : ℕ) : ℕ := (2 * n + 1) ^ 2

theorem main :
    (∀ n : ℕ, 1 < n → a n = (1 + 2 * n) ^ 2 ∧ a n = A016754 n) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * (a (n-1) : ℤ) - 3 * (a (n-2) : ℤ) + (a (n-3) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 =
      1 + 5 * PowerSeries.X + 4 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3
        + PowerSeries.X ^ 4) := by sorry

end OMA.S_oeis_a273743
