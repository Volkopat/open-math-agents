import Mathlib

/-!
# A188861: Number of n X 4 binary arrays without the pattern 0 1 diagonally, vertically or antidiagonally.

Source: https://oeis.org/A188861
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (by R. H. Hardin, Apr 12 2011; column 4 of A188866; DATA 16, 41, 68, 95, 122, ...) records in its
FORMULA section:

  Empirical: a(n) = 27*n - 13 for n>1.
  Conjectures from Colin Barker, Feb 28 2018:
  G.f.: x*(16 + 9*x + 2*x^2) / (1 - x)^2.
  a(n) = 2*a(n-1) - a(n-2) for n>3.

Conventions:
* Offset 1: `a n` is defined for every `n`, and the conjecture concerns `n ≥ 1`.
* An `n X 4` binary array is a function `x : Fin n → Fin 4 → Fin 2`, where `x i c` is the
  entry in row `i` and column `c`.
* The array contains the pattern 0 1 vertically, diagonally or antidiagonally when some entry
  `x i c = 0` has, in the next row `i + 1`, an entry `x (i+1) d = 1` in column `d = c`
  (vertically), `d = c + 1` (diagonally) or `d + 1 = c` (antidiagonally). Reading the pattern
  the other way up (1 above 0) gives the same count, by complementing all entries and reversing
  the order of the rows.
* `a n` is the number of `n X 4` binary arrays avoiding the pattern, computed as the cardinality
  of a finite filter; it is not defined from any formula.
* The g.f. x*(16 + 9*x + 2*x^2)/(1 - x)^2 has coefficients 16, 41, 68 and then increases by 27,
  so the g.f. conjecture, the empirical formula and the recurrence together are equivalent to:
  `a 1 = 16` and `a n = 27 * n - 13` for all `n ≥ 2`. This is what `main` asserts.
-/

namespace OMA.S_oeis_a188861

/-- The array `x` contains a 0 with a 1 directly below it, or diagonally or antidiagonally
below it, in the next row. -/
def HasPattern {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Prop :=
  ∃ i j : Fin n, j.val = i.val + 1 ∧ ∃ c d : Fin 4,
    (d.val = c.val ∨ d.val = c.val + 1 ∨ c.val = d.val + 1) ∧ x i c = 0 ∧ x j d = 1

instance {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Decidable (HasPattern x) := by
  unfold HasPattern; infer_instance

/-- The number of `n X 4` binary arrays without the pattern 0 1 vertically, diagonally or
antidiagonally. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 4 → Fin 2 => ¬ HasPattern x)).card

/-- The conjecture of A188861: `a 1 = 16` and `a n = 27 * n - 13` for `n ≥ 2` (equivalently,
the g.f. is x*(16 + 9*x + 2*x^2)/(1 - x)^2). -/
theorem main : a 1 = 16 ∧ ∀ n : ℕ, 2 ≤ n → a n = 27 * n - 13 := by
  sorry

end OMA.S_oeis_a188861
