import Mathlib

/-!
# OEIS A270088: Number of active (ON, black) cells at stage 2^n - 1 of Rule 73

Source: https://oeis.org/A270088
Conjectures: Lars Blomberg, Apr 21 2016; Colin Barker, Apr 21 2016.
Formalization: @longling12 (drafted with AI assistance)

Entry A270088 (Robert Price, Mar 10 2016), offset 0: Number of active (ON, black) cells at stage
`2^n - 1` of the two-dimensional cellular automaton defined by Rule 73, based on the 5-celled von
Neumann neighborhood, initialized with a single black (ON) cell at stage zero.

Formalization notes:
* Outer-totalistic 5-cell von Neumann rule 73 on `ℤ × ℤ` (Rule 73 has bit 0 equal to 1, so the
  infinite background alternates between OFF and ON).
* Because the neighborhood has `L^∞` radius 1, at stage `t` every cell outside `[-t, t]^2` shares
  a uniform background state `bg`; `stageCfg` evolves `(bg, rows)` synchronously on `ℤ × ℤ` and
  `countOn` counts ON cells in `[-t, t]^2` as in `%t`, giving `1, 4, 40, 225, 961, 3969, ...` at
  `t = 2^n - 1`.
-/

namespace OMA.S_oeis_a270088

open PowerSeries

/-- One cell update of outer-totalistic `Rule r` on the 5-cell von Neumann neighborhood. -/
def applyRule (r : ℕ) (c n s w e : Bool) : Bool :=
  r.testBit (c.toNat + 2 * (n.toNat + s.toNat + w.toNat + e.toNat))

/-- Read cell `(x, y)` of a stage-`t` configuration `(bg, rows)`, where `rows` stores the central
`(2t + 1) × (2t + 1)` square `[-t, t]^2` (indexed by `y + t`, `x + t`) and every cell outside
`[-t, t]^2` has the uniform background state `bg`. -/
def getCell (t : ℕ) (c : Bool × List (List Bool)) (x y : ℤ) : Bool :=
  if -↑t ≤ x ∧ x ≤ ↑t ∧ -↑t ≤ y ∧ y ≤ ↑t then
    (c.2.getD (y + ↑t).toNat []).getD (x + ↑t).toNat c.1
  else c.1

/-- One synchronous step on `ℤ × ℤ` from stage `t` to stage `t + 1`. -/
def stepCfg (r t : ℕ) (c : Bool × List (List Bool)) : Bool × List (List Bool) :=
  let g := getCell t c
  (applyRule r c.1 c.1 c.1 c.1 c.1,
   (List.range (2 * (t + 1) + 1)).map fun iy =>
     (List.range (2 * (t + 1) + 1)).map fun ix =>
       let x : ℤ := (ix : ℤ) - ↑(t + 1)
       let y : ℤ := (iy : ℤ) - ↑(t + 1)
       applyRule r (g x y) (g x (y - 1)) (g x (y + 1)) (g (x - 1) y) (g (x + 1) y))

/-- Configuration at stage `t` started from a single ON cell at `(0, 0)` on an all-OFF plane. -/
def stageCfg (r : ℕ) : ℕ → Bool × List (List Bool)
  | 0 => (false, [[true]])
  | t + 1 => stepCfg r t (stageCfg r t)

/-- Number of ON cells in `[-t, t]^2` at stage `t` of `Rule r`. -/
def countOn (r t : ℕ) : ℕ :=
  ((stageCfg r t).2.map fun row => row.count true).sum

/-- `A270088(n)`: number of ON cells in `[-(2^n - 1), 2^n - 1]^2` at stage `2^n - 1` of Rule 73. -/
def a (n : ℕ) : ℕ := countOn 73 (2 ^ n - 1)

theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 4 * 4 ^ n - 4 * 2 ^ n + 1) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      1 - 3 * X + 26 * X ^ 2 - 7 * X ^ 3 - 86 * X ^ 4 + 72 * X ^ 5 := by
  sorry

end OMA.S_oeis_a270088
