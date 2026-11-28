import Mathlib

/-!
# A266219: Binary representation of the middle column of the "Rule 7" elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266219 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry A266219 (Robert Price, Dec 24 2015), offset 0. Formula section, verbatim:
Conjectures from Colin Barker, Dec 25 2015 and Apr 13 2019:
a(n) = 1/198*(-9*(-1)^n+109*2^(n+1)*5^n-11).
a(n) = 10*a(n-1) + a(n-2) - 10*a(n-3) for n>2.
G.f.: (1+x-x^2) / ((1-x)*(1+x)*(1-10*x)).
Conjecture: a(n) = floor(109*10^n/99). - Karl V. Keller, Jr., Mar 16 2022

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 7 maps 000 to ON).
* Counting convention: a(n) writes the middle cells (cell 0) of stages 0..n as binary digits,
  stage 0 first (most significant), and reads them in base 10, as the entry's data shows
  (1, 11, 110, 1101, ...).
* The statement is the conjunction of the four conjectures. The closed form and the floor
  formula carry no range in the entry, so they are stated for every n >= 0 (the offset);
  the recurrence is stated for n > 2, as printed. The closed form is stated in the rationals,
  the recurrence in the integers, and the floor formula with the floor of a rational number.
  The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power series ring over
  the rationals, and the identity is A = N * D⁻¹, where D has constant term 1.
* Controls from the entry: the definition gives 1, 11, 110, 1101, 11010, 110101, 1101010 for
  n = 0..6, matching the entry's data.
-/

namespace OMA.S_oeis_a266219

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The middle cell of stage n of Rule 7. -/
def c (n : ℕ) : ℕ := (state 7 n 0).toNat

/-- A266219(n): the middle cells of stages 0..n as binary digits, stage 0 first, read in base 10. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), c k * 10 ^ (n - k)

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function and Keller's floor formula for
OEIS A266219. -/
theorem main :
    (∀ n : ℕ, (a n : ℚ) = 1 / 198 * (-9 * (-1) ^ n + 109 * 2 ^ (n + 1) * 5 ^ n - 11)) ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)) ∧
    A = (1 + X - X ^ 2) * ((1 - X) * (1 + X) * (1 - 10 * X))⁻¹ ∧
    (∀ n : ℕ, (a n : ℤ) = ⌊(109 * 10 ^ n / 99 : ℚ)⌋) := by
  sorry

end OMA.S_oeis_a266219
