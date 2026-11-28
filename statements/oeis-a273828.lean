import Mathlib

/-!
# OEIS A273828: Blomberg's conjectures for Rule 950 at stages 2^n - 1

Source: https://oeis.org/A273828
Conjectures: Lars Blomberg, Jul 25 2016.
Formalization: @longling12 (drafted with AI assistance)

Entry A273828 (Robert Price, May 31 2016), offset 0: Number of active (ON, black) cells at stage
`2^n - 1` of the two-dimensional cellular automaton defined by Rule 950, based on the 5-celled von
Neumann neighborhood, initialized with a single black (ON) cell at stage zero.

Formalization notes:
* Outer-totalistic 5-cell von Neumann rules 950 and 1014 on `ℤ × ℤ`.
* Because the neighborhood has `L^∞` radius 1, at stage `t` every cell outside `[-t, t]^2` shares
  a uniform background state `bg`; `stageCfg` evolves `(bg, rows)` synchronously on `ℤ × ℤ` and
  `countOn` counts ON cells in `[-t, t]^2` as in `%t`, reproducing `1, 5, 25, 109, 477, 1981, ...`.
* Rule 1014 also generates this sequence means `countOn 1014 (2 ^ n - 1) = a n` for every `n`.
-/

namespace OMA.S_oeis_a273828

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

/-- `A273828(n)`: number of ON cells in `[-(2^n - 1), 2^n - 1]^2` at stage `2^n - 1` of Rule 950. -/
def a (n : ℕ) : ℕ := countOn 950 (2 ^ n - 1)

theorem main :
    (∀ n : ℕ, countOn 1014 (2 ^ n - 1) = a n) ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 2 * 4 ^ n - 2 * 2 ^ n - 3) := by
  sorry

end OMA.S_oeis_a273828
