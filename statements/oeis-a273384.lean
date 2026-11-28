import Mathlib

/-!
# A273384: Number of active (ON, black) cells in n-th stage of growth of two-dimensional
cellular automaton defined by "Rule 659", based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A273384
Credit: @Salofe

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.

The conjectures, quoted verbatim from the FORMULA section of the entry:

  Conjectures from _Colin Barker_, May 21 2016: (Start)
  a(n) = (1+2*n)^2 for n>2.
  a(n) = 3*a(n-1)-3*a(n-2)+a(n-3) for n>5.
  G.f.: (1+2*x+5*x^2+12*x^3-20*x^4+8*x^5) / (1-x)^3.
  (End)

Formalization notes:
* Offset 0 (comment of the entry: "Initialized with a single black (ON) cell at stage zero"):
  stage 0 is a single ON cell at the origin of the infinite grid ℤ × ℤ, every other cell OFF,
  and stage n+1 is obtained from stage n by one synchronous update of every cell, the infinite
  background included.
* Rule 659 is read in Wolfram's numbering of the 5-neighbour outer totalistic rules, as in the
  entry's Mathematica program (rule = IntegerDigits[659,2,10], rule[[10-#]] applied to
  ListConvolve with kernel {{0,2,0},{2,1,2},{0,2,0}}): a cell whose own value is c (0 or 1)
  and which has k ON cells among its four orthogonal neighbours becomes bit c + 2*k of 659
  (bit 0 is the least significant one). Bit 0 of 659 is 1, so the OFF background turns ON at
  stage 1.
* As in the published Mathematica program (stage n is trimmed to the (2n+1) × (2n+1) square
  centred on the initial cell, Part[..., Range[k+1-n, k-1+n]], before the cell values are
  added up), a(n) is the number of ON cells (x, y) with -n ≤ x ≤ n and -n ≤ y ≤ n at stage n.
  The program evolves a finite cyclic grid of side 2*128+1; on these squares it agrees with the
  infinite grid used here. This convention reproduces all 129 terms of the b-file
  (n = 0..128).
* First conjunct: the closed form for n > 2, exactly the range of the conjecture, read in ℕ
  (it involves no subtraction).
* Second conjunct: the recurrence for n > 5, exactly the range of the conjecture; there n - 1,
  n - 2 and n - 3 are exact natural-number subtractions, and the identity is read in ℤ.
* Third conjunct: the generating function, written as the product identity
  A(x) * (1-x)^3 = 1+2x+5x^2+12x^3-20x^4+8x^5 in ℤ⟦X⟧, where A(x) = Σ a(n) x^n. The factor
  (1-x)^3 has constant coefficient 1, hence is invertible in ℤ⟦X⟧, so the identity is
  equivalent to the quotient form of the conjecture and needs no division.
-/
namespace OMA.S_oeis_a273384

/-- A configuration of the plane: `g x y` is the value of the cell `(x, y)` (true = ON). -/
abbrev Grid := ℤ → ℤ → Bool

def bit (b : Bool) : ℕ := if b then 1 else 0

/-- Rule 659: a cell with own value `c` and `k` ON orthogonal neighbours becomes
bit `bit c + 2 * k` of 659. -/
def rule (c : Bool) (k : ℕ) : Bool :=
  decide ((659 / 2 ^ (bit c + 2 * k)) % 2 = 1)

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

theorem main :
    (∀ n : ℕ, 2 < n → a n = (1 + 2 * n) ^ 2) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * (a (n-1) : ℤ) - 3 * (a (n-2) : ℤ) + (a (n-3) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 =
      1 + 2 * PowerSeries.X + 5 * PowerSeries.X ^ 2 + 12 * PowerSeries.X ^ 3
        - 20 * PowerSeries.X ^ 4 + 8 * PowerSeries.X ^ 5) := by sorry

end OMA.S_oeis_a273384
