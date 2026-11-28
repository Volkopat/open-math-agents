import Mathlib

/-!
# OEIS A272921: Blomberg's and Barker's conjectures for Rule 555 at stages 2^n - 1

Source: https://oeis.org/A272921
Conjectures: Lars Blomberg, Jul 10 2016; Colin Barker, Dec 01 2016.
Formalization: @longling12 (drafted with AI assistance)

Entry A272921 (Robert Price, May 10 2016), offset 0: Number of active (ON, black) cells at stage
2^n - 1 of the two-dimensional cellular automaton defined by Rule 555, based on the 5-celled von
Neumann neighborhood, initialized with a single black (ON) cell at stage zero.
Conjecture: Rule 571 also generates this sequence. - Lars Blomberg, Jul 10 2016.
Conjecture: a(n) = 3*4^n - 4*3^(n-2) - 4*2^n + 1, n>1. - Lars Blomberg, Jul 10 2016.
Conjectures from Colin Barker, Dec 01 2016:
a(n) = 10*a(n-1) - 35*a(n-2) + 50*a(n-3) - 24*a(n-4) for n>5.
G.f.: (1 - 5*x + 14*x^2 - 16*x^3 - 32*x^4 + 32*x^5) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)).

Formalization notes:
* Outer-totalistic 5-cell von Neumann Rules 555 and 571 on Z x Z.
* Because the neighborhood has L^infty radius 1, at stage t every cell outside [-t, t]^2 shares a
  uniform background state bg; stageCfg evolves (bg, rows) synchronously on Z x Z and countOn
  counts ON cells in [-t, t]^2 as in %t, reproducing 1, 5, 29, 149, 669, 2837, ...
* Rule 571 also generates this sequence means countOn 571 (2 ^ n - 1) = a n for every n; the closed
  form (for n > 1, where n - 2 >= 0) and recurrence are stated over Z, and the generating function
  is stated in PowerSeries Z since D(0) = 1.
-/

namespace OMA.S_oeis_a272921

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

/-- A272921(n): number of ON cells in [-(2^n - 1), 2^n - 1]^2 at stage 2^n - 1 of Rule 555. -/
def a (n : ℕ) : ℕ := countOn 555 (2 ^ n - 1)

/-- Blomberg's and Barker's conjectures for A272921. -/
theorem main :
    (∀ n : ℕ, countOn 571 (2 ^ n - 1) = a n) ∧
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 3 * 4 ^ n - 4 * 3 ^ (n - 2) - 4 * 2 ^ n + 1) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 10 * a (n - 1) - 35 * a (n - 2) + 50 * a (n - 3) - 24 * a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
      1 - 5 * X + 14 * X ^ 2 - 16 * X ^ 3 - 32 * X ^ 4 + 32 * X ^ 5 := by
  sorry

end OMA.S_oeis_a272921
