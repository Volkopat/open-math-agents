import Mathlib

/-!
# A267879: Binary representation of the middle column of the "Rule 233" elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267879 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry A267879 (Robert Price, Jan 21 2016), offset 0. Formula section, verbatim:
Conjectures from Colin Barker, Jan 22 2016 and Apr 20 2019:
a(n) = 11*a(n-1)-10*a(n-2) for n>4.
G.f.: (1-x+x^2-x^3+x^4) / ((1-x)*(1-10*x)).
Conjecture: a(n) = (9091*10^(n-3) - 1)/9 for n > 2. - Stefano Spezia, Dec 25 2021

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 233 maps 000 to ON).
* Counting convention: a(n) writes the middle cells (cell 0) of stages 0..n as binary digits,
  stage 0 first (most significant), and reads them in base 10, as the entry's data shows
  (1, 10, 101, 1010, ...).
* The statement is the conjunction of the three conjectures, on the ranges the entry gives.
  The recurrence is stated in the integers and the closed form in the rationals (n - 3 is
  natural-number subtraction, exact for n > 2). The generating function is
  A(x) = Sum_{n >= 0} a(n) x^n in the formal power series ring over the rationals, and the
  identity is A = N * D⁻¹, where D has constant term 1.
* Controls from the entry: the definition gives 1, 10, 101, 1010, 10101, 101011, 1010111 for
  n = 0..6, matching the entry's data.
-/

namespace OMA.S_oeis_a267879

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The middle cell of stage n of Rule 233. -/
def c (n : ℕ) : ℕ := (state 233 n 0).toNat

/-- A267879(n): the middle cells of stages 0..n as binary digits, stage 0 first, read in base 10. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), c k * 10 ^ (n - k)

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function and Spezia's closed form for OEIS A267879. -/
theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2)) ∧
    A = (1 - X + X ^ 2 - X ^ 3 + X ^ 4) * ((1 - X) * (1 - 10 * X))⁻¹ ∧
    (∀ n : ℕ, 2 < n → (a n : ℚ) = (9091 * 10 ^ (n - 3) - 1) / 9) := by
  sorry

end OMA.S_oeis_a267879
