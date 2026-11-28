import Mathlib

/-!
# OEIS A269811: Barker's conjectures for Rule 33 at stages 2^n - 1

Source: https://oeis.org/A269811
Conjectures: Colin Barker, Apr 15 2016.
Formalization: @longling12 (drafted with AI assistance)

Entry A269811 (Robert Price, Mar 05 2016), offset 0: Number of active (ON, black) cells at stage
2^n - 1 of the two-dimensional cellular automaton defined by Rule 33, based on the 5-celled von
Neumann neighborhood, initialized with a single black (ON) cell at stage zero.
Conjectures from Colin Barker, Apr 15 2016:
a(n) = -2+(-1)^n/3-(5*2^(1+n))/3-5*3^(-2+n)+13*4^(-1+n) for n>1.
a(n) = (117*2^(2*n)-15*2^(n+3)-20*3^n-60)/36 for n>1 and even.
a(n) = (117*2^(2*n)-15*2^(n+3)-20*3^n-84)/36 for n>1 and odd.
G.f.: (1-5*x+21*x^2-39*x^3-30*x^4+36*x^5+40*x^6) / ((1-x)*(1+x)*(1-2*x)*(1-3*x)*(1-4*x)).

Formalization notes:
* Outer-totalistic 5-cell von Neumann Rule 33 on Z x Z.
* Because the neighborhood has L^infty radius 1, at stage t every cell outside [-t, t]^2 shares a
  uniform background state bg; stageCfg evolves (bg, rows) synchronously on Z x Z and countOn
  counts ON cells in [-t, t]^2 as in %t, reproducing 1, 4, 32, 164, 732, 3084, ...
* The first closed form has rational coefficients and is stated over Q; in the even and odd closed
  forms for n > 1, division by 36 is exact in Z; the generating function is stated as A(x) * D(x) =
  N(x) in PowerSeries Z since D(0) = 1.
-/

namespace OMA.S_oeis_a269811

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

/-- A269811(n): number of ON cells in [-(2^n - 1), 2^n - 1]^2 at stage 2^n - 1 of Rule 33. -/
def a (n : ℕ) : ℕ := countOn 33 (2 ^ n - 1)

/-- Barker's closed forms and generating function conjectures for A269811. -/
theorem main :
    (∀ n : ℕ, 1 < n →
      (a n : ℚ) = -2 + (-1 : ℚ) ^ n / 3 - (5 * 2 ^ (1 + n)) / 3 -
        5 * (3 : ℚ) ^ (-2 + (n : ℤ)) + 13 * (4 : ℚ) ^ (-1 + (n : ℤ))) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 0 →
      (a n : ℤ) = (117 * 2 ^ (2 * n) - 15 * 2 ^ (n + 3) - 20 * 3 ^ n - 60) / 36) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 1 →
      (a n : ℤ) = (117 * 2 ^ (2 * n) - 15 * 2 ^ (n + 3) - 20 * 3 ^ n - 84) / 36) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
      1 - 5 * X + 21 * X ^ 2 - 39 * X ^ 3 - 30 * X ^ 4 + 36 * X ^ 5 + 40 * X ^ 6 := by
  sorry

end OMA.S_oeis_a269811
