import Mathlib

/-!
# A267872: Number of ON (black) cells in the n-th iteration of the "Rule 237" elementary
cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267872
Credit: @Salofe

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.

The conjecture, quoted verbatim from the FORMULA section of the entry:

  Conjectures from _Colin Barker_, Jan 22 2016 and Apr 20 2019: (Start)
  a(n) = 2*a(n-1)-a(n-2) for n>3.
  G.f.: (1-x+4*x^2-2*x^3) / (1-x)^2.
  (End)

Formalization notes:
* Offset 0: a(0) counts the initial row, a single ON cell at position 0 on an infinite OFF
  background, and a(n) counts the row obtained after n applications of the rule.
* Standard Wolfram orientation: a cell whose left neighbour, own state and right neighbour are
  l, c, r becomes bit 4*l + 2*c + r of the rule number 237 (left weight 4, centre 2, right 1).
* The rule is applied on the whole line ℤ, background included. Rule 237 sends 000 to 1, so the
  OFF background turns ON at time 1. As in the published Mathematica program (row k is cropped
  to positions rows-k+1 .. rows+k-1 before Total), the count at time n is taken over the cells
  -n .. n only, the light cone of the initial cell. This convention reproduces all 1001 terms of
  the b-file (n = 0..1000), and it is the convention of statements/oeis-a267622.lean (Rule 187).
* The first conjunct is the recurrence for n > 3, exactly the range of the conjecture; there
  n - 1 and n - 2 are exact natural-number subtractions, and the identity is read in ℤ.
* The second conjunct is the generating function, written as the product identity
  A(x) * (1-x)^2 = 1-x+4x^2-2x^3 in ℤ⟦X⟧, where A(x) = Σ a(n) x^n. The factor (1-x)^2 has
  constant coefficient 1, hence is invertible in ℤ⟦X⟧, so the identity is equivalent to the
  quotient form of the conjecture and needs no division.
-/
namespace OMA.S_oeis_a267872

abbrev Row := ℤ → Bool

def bit (b : Bool) : ℕ := if b then 1 else 0

/-- Wolfram rule 237: the new state is bit `4*l + 2*c + r` of 237. -/
def rule (l c r : Bool) : Bool :=
  decide ((237 / 2 ^ (4 * bit l + 2 * bit c + bit r)) % 2 = 1)

/-- One synchronous update of the whole line. -/
def step (g : Row) : Row := fun x => rule (g (x-1)) (g x) (g (x+1))

/-- A single ON cell at position 0, every other cell OFF. -/
def initial : Row := fun x => decide (x = 0)

/-- The row at time n. -/
def state : ℕ → Row
  | 0 => initial
  | n+1 => step (state n)

/-- The number of ON cells among positions -n .. n at time n. (Marked noncomputable only
because Mathlib's order instance on ℤ used by `Finset.Icc` is noncomputable.) -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun x => state n x = true)).card

theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 2 * (a (n-1) : ℤ) - (a (n-2) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X)^2 =
      1 - PowerSeries.X + 4 * PowerSeries.X^2 - 2 * PowerSeries.X^3) := by sorry

end OMA.S_oeis_a267872
