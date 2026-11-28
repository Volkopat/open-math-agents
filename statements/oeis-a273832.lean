import Mathlib

/-!
# OEIS A273832: Blomberg's other rules and closed form and Mathar's identification for Rule 961

Source: https://oeis.org/A273832 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A273832 (Robert Price, May 31 2016), offset 0: Number of active (ON, black) cells at stage
2^n-1 of the two-dimensional cellular automaton defined by Rule 961, based on the 5-celled von
Neumann neighborhood.
Formula section:
Conjecture: Rule 977 also generates this sequence. - Lars Blomberg, Jul 25 2016
Conjecture: a(n) = A269911(n) for n>1. - R. J. Mathar, Jun 02 2016
Conjecture: a(n) = 4*4^n - 4*2^n - 3, n>1. - Lars Blomberg, Jul 25 2016

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 961
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Counting convention: a(n) is the number of ON cells of stage 2^n - 1 in the square [-(2^n - 1),
  2^n - 1]^2, as the entry's program counts it (it trims each stage s to the square [-s, s]^2 and
  takes the counts at the stages 2^n - 1).
* Other codes: ruleOf, stateOf and aOf are rule, state and a with the code r in place of 961, so
  rule unfolds to ruleOf 961 and a to aOf 961; a statement that Rule r also generates this sequence
  is stated as aOf r n = a n for every n.
* A269911 is, by its name (Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional
  cellular automaton defined by Rule 3, based on the 5-celled von Neumann neighborhood), aOf 3; its
  listed terms a(0..1) = 1, 5 are controls (theorem controls_A269911).
* The statement is the conjunction of the 3 conjectures of the site's problem, in the entry's order.
  The closed form is stated in the rationals, where every division is exact.
* Not part of the site's problem, so not stated here: the formula line by Colin Barker.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..2 equal to
  the entry's first 3 terms, 1, 4, 45.
-/

namespace OMA.S_oeis_a273832

open PowerSeries

/-- Rule 961: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 961). -/
def rule (c : Bool) (k : ℕ) : Bool := (961 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A273832(n): the number of ON cells of stage `2^n - 1` in the square `[-(2^n-1), 2^n-1]²`. -/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if state (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0

/-- The outer totalistic rule with code `r`: bit `2k + c` of `r`, as `rule` is for this entry. -/
def ruleOf (r : ℕ) (c : Bool) (k : ℕ) : Bool := r.testBit (2 * k + cond c 1 0)

/-- The automaton with code `r` on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def stateOf (r : ℕ) : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => ruleOf r (stateOf r t p) ((nbrs p).countP (fun q => stateOf r t q))

/-- The same count as `a` for the automaton with code `r`. -/
def aOf (r n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if stateOf r (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0

/-- Blomberg's other rules and closed form and Mathar's identification. -/
theorem main :
    (∀ n : ℕ, aOf 977 n = a n) ∧
    (∀ n : ℕ, 1 < n → a n = aOf 3 n) ∧
    (∀ n : ℕ, 1 < n → (a n : ℚ) = 4 * 4 ^ n - 4 * 2 ^ n - 3) := by
  sorry

end OMA.S_oeis_a273832
