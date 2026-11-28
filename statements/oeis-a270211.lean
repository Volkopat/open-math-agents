import Mathlib

/-!
# OEIS A270211: Blomberg's conjecture for Rule 123 at stages 2^n - 1

Source: https://oeis.org/A270211
Conjecture: Lars Blomberg, Apr 30 2016.
Formalization: @longling12 (drafted with AI assistance)

Entry A270211 (Robert Price, Mar 13 2016), offset 0: Number of active (ON, black) cells at stage
2^n - 1 of the two-dimensional cellular automaton defined by Rule 123, based on the 5-celled von
Neumann neighborhood, initialized with a single black (ON) cell at stage zero.
Conjecture: a(n) = (14*4^(n-1) + 124*3^(n-3) - 159*2^(n-2) + 615)/3, n>5. - Lars Blomberg, Apr 30
2016.

Formalization notes:
* Outer-totalistic 5-cell von Neumann Rule 123 on Z x Z.
* Because the neighborhood has L^infty radius 1, at stage t every cell outside [-t, t]^2 shares a
  uniform background state bg; stageCfg evolves (bg, rows) synchronously on Z x Z and countOn
  counts ON cells in [-t, t]^2 as in %t, reproducing 1, 5, 41, 209, 913, 3697, ...
* Division by 3 in the conjectured closed form is stated over Q so that non-divisible numerators
  are not rounded by integer division.
-/

namespace OMA.S_oeis_a270211

/-- One cell update of outer-totalistic Rule r on the 5-cell von Neumann neighborhood. -/
def applyRule (r : ℕ) (c n s w e : Bool) : Bool :=
  r.testBit (c.toNat + 2 * (n.toNat + s.toNat + w.toNat + e.toNat))

/-- Read cell (x, y) of a stage-t configuration (bg, rows), where rows stores [-t, t]^2 and every
cell outside [-t, t]^2 has the uniform background state bg. -/
def getCell (t : ℕ) (c : Bool × List (List Bool)) (x y : ℤ) : Bool :=
  if -↑t ≤ x ∧ x ≤ ↑t ∧ -↑t ≤ y ∧ y ≤ ↑t then
    (c.2.getD (y + ↑t).toNat []).getD (x + ↑t).toNat c.1
  else c.1

/-- One synchronous step on Z x Z from stage t to stage t + 1. -/
def stepCfg (r t : ℕ) (c : Bool × List (List Bool)) : Bool × List (List Bool) :=
  let g := getCell t c
  (applyRule r c.1 c.1 c.1 c.1 c.1,
   (List.range (2 * (t + 1) + 1)).map fun iy =>
     (List.range (2 * (t + 1) + 1)).map fun ix =>
       let x : ℤ := (ix : ℤ) - ↑(t + 1)
       let y : ℤ := (iy : ℤ) - ↑(t + 1)
       applyRule r (g x y) (g x (y - 1)) (g x (y + 1)) (g (x - 1) y) (g (x + 1) y))

/-- Configuration at stage t started from a single ON cell at (0, 0) on an all-OFF plane. -/
def stageCfg (r : ℕ) : ℕ → Bool × List (List Bool)
  | 0 => (false, [[true]])
  | t + 1 => stepCfg r t (stageCfg r t)

/-- Number of ON cells in [-t, t]^2 at stage t of Rule r. -/
def countOn (r t : ℕ) : ℕ :=
  ((stageCfg r t).2.map fun row => row.count true).sum

/-- A270211(n): number of ON cells in [-(2^n - 1), 2^n - 1]^2 at stage 2^n - 1 of Rule 123. -/
def a (n : ℕ) : ℕ := countOn 123 (2 ^ n - 1)

/-- Blomberg's closed-form conjecture for A270211. -/
theorem main :
    ∀ n : ℕ, 5 < n →
      (a n : ℚ) = (14 * 4 ^ (n - 1) + 124 * 3 ^ (n - 3) - 159 * 2 ^ (n - 2) + 615) / 3 := by
  sorry

end OMA.S_oeis_a270211
