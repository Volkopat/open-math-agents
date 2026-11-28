import Mathlib

/-!
# OEIS A271804: Blomberg's and Barker's conjectures for Rule 401 at stages 2^n - 1

Source: https://oeis.org/A271804
Conjectures: Lars Blomberg, Jun 22 2016; Colin Barker, Jun 22 2016.
Formalization: @longling12 (drafted with AI assistance)

Entry A271804 (Robert Price, Apr 15 2016), offset 0: Number of active (ON, black) cells at stage
2^n - 1 of the two-dimensional cellular automaton defined by Rule 401, based on the 5-celled von
Neumann neighborhood, initialized with a single black (ON) cell at stage zero.
Conjecture: Rule 409 also generates this sequence. - Lars Blomberg, Jun 22 2016.
Conjectures from Colin Barker, Jun 22 2016:
a(n) = (1-2^(2+n)+4^(1+n)+(2^(-1-n)*(-(3-sqrt(17))^n*(-7+sqrt(17))-(3+sqrt(17))^n*(7+sqrt(17))))/sqrt(17)) for n>0.
G.f.: (1-6*x+25*x^2-60*x^3+12*x^4+16*x^5) / ((1-x)*(1-2*x)*(1-4*x)*(1-3*x-2*x^2)).

Formalization notes:
* Outer-totalistic 5-cell von Neumann Rules 401 and 409 on Z x Z.
* Because the neighborhood has L^infty radius 1, at stage t every cell outside [-t, t]^2 shares a
  uniform background state bg; stageCfg evolves (bg, rows) synchronously on Z x Z and countOn
  counts ON cells in [-t, t]^2 as in %t, reproducing 1, 4, 32, 164, 744, 3196, ...
* Rule 409 also generates this sequence means countOn 409 (2 ^ n - 1) = a n for every n; Barker's
  radical closed form is stated over R using Real.sqrt 17, and his generating function is stated in
  PowerSeries Z since D(0) = 1.
-/

namespace OMA.S_oeis_a271804

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

/-- A271804(n): number of ON cells in [-(2^n - 1), 2^n - 1]^2 at stage 2^n - 1 of Rule 401. -/
def a (n : ℕ) : ℕ := countOn 401 (2 ^ n - 1)

/-- Blomberg's and Barker's conjectures for A271804. -/
theorem main :
    (∀ n : ℕ, countOn 409 (2 ^ n - 1) = a n) ∧
    (∀ n : ℕ, 0 < n →
      (a n : ℝ) = 1 - 2 ^ (2 + n) + 4 ^ (1 + n) +
        ((2 : ℝ) ^ (-1 - (n : ℤ)) *
          (-(3 - Real.sqrt 17) ^ n * (-7 + Real.sqrt 17) -
            (3 + Real.sqrt 17) ^ n * (7 + Real.sqrt 17))) / Real.sqrt 17) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 4 * X) * (1 - 3 * X - 2 * X ^ 2)) =
      1 - 6 * X + 25 * X ^ 2 - 60 * X ^ 3 + 12 * X ^ 4 + 16 * X ^ 5 := by
  sorry

end OMA.S_oeis_a271804
