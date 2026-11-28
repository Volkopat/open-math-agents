import Mathlib

/-!
# OEIS A272832: Blomberg's and Spezia's conjectures for Rule 694 at stages 2^n - 1

Source: https://oeis.org/A272832
Conjectures: Lars Blomberg, Jul 19 2016; Stefano Spezia, Jun 07 2025.
Formalization: @longling12 (drafted with AI assistance)

Entry A272832 (Robert Price, May 19 2016), offset 0: Number of active (ON, black) cells at stage
2^n - 1 of the two-dimensional cellular automaton defined by Rule 694, based on the 5-celled von
Neumann neighborhood, initialized with a single black (ON) cell at stage zero.
Conjecture: a(n) = 2*4^n - 16*3^(n-2) + 2^(n-1) + 1, n>2. - Lars Blomberg, Jul 19 2016.
Conjectured g.f.: (1 - 5*x + 6*x^2 + 36*x^4 - 92*x^5 + 48*x^6)/((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)).
- Stefano Spezia, Jun 07 2025.

Formalization notes:
* Outer-totalistic 5-cell von Neumann Rule 694 on Z x Z.
* Because the neighborhood has L^infty radius 1, at stage t every cell outside [-t, t]^2 shares a
  uniform background state bg; stageCfg evolves (bg, rows) synchronously on Z x Z and countOn
  counts ON cells in [-t, t]^2 as in %t, reproducing 1, 5, 21, 85, 377, 1633, ...
* The closed form (for n > 2, where n - 2 >= 1 and n - 1 >= 2) is stated over Z, and the generating
  function is stated in PowerSeries Z since D(0) = 1.
-/

namespace OMA.S_oeis_a272832

open PowerSeries

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

/-- A272832(n): number of ON cells in [-(2^n - 1), 2^n - 1]^2 at stage 2^n - 1 of Rule 694. -/
def a (n : ℕ) : ℕ := countOn 694 (2 ^ n - 1)

/-- Blomberg's and Spezia's conjectures for A272832. -/
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 2 * 4 ^ n - 16 * 3 ^ (n - 2) + 2 ^ (n - 1) + 1) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
      1 - 5 * X + 6 * X ^ 2 + 36 * X ^ 4 - 92 * X ^ 5 + 48 * X ^ 6 := by
  sorry

end OMA.S_oeis_a272832
