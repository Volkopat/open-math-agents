import Mathlib

/-!
# A246317: Rule 452 at stages `2^n - 1`, and the rules that generate the same sequence

Source: https://oeis.org/A246317
Credit: @avivorly

A246316 (%N): Total number of ON cells at stage n of two-dimensional 5-neighbor outer totalistic cellular automaton
defined by "Rule 452".

A246317 (%N): A246316(2^n-1).

The convention is fixed by the Mathematica program of A246316 (%t):
`CellularAutomaton[{452, {2, {{0, 2, 0}, {2, 1, 2}, {0, 2, 0}}}, {1, 1}}, {{{1}}, 0}, n]`
(weight 1 on the cell itself and weight 2 on each of its 4 von Neumann neighbours; stage 0 is a single ON cell).

Conjecture (Lars Blomberg, Jun 14 2016, in A246317): Conjecture: Rules 332, 356, 364, 452, 460, 484, 492, 836, 844,
868, 876, 964, 972, 996 and 1004 also generate this sequence.

Conventions:
- Cells are the points of `ℤ × ℤ`; a configuration is the finite set of its ON cells. The 4 von Neumann neighbours of
  `(x, y)` are `(x + 1, y)`, `(x - 1, y)`, `(x, y + 1)`, `(x, y - 1)`.
- Rule `r`: a cell with own state `c` (1 if ON, 0 if OFF) and `k` ON neighbours (`0 ≤ k ≤ 4`) is ON at the next stage
  iff bit `c + 2 * k` of `r` is set (`Nat.testBit r (2 * k + c)`): this is the weighted sum of the Mathematica kernel
  above, read as a binary digit of the rule number.
- `step r S` evaluates this rule on the finite window made of the cells of `S` and their neighbours. Every cell outside
  that window has `c = 0` and `k = 0`, so its next state is bit 0 of `r`. Every rule number in the conjecture (and
  452) is even, so bit 0 is clear and those cells stay OFF: for these rules `step r` is exactly one step of the rule
  on the whole infinite grid.
- Stage 0 is the single ON cell `(0, 0)`; `stage r n` is the configuration after `n` steps. `A246316 n` is the number
  of ON cells of `stage 452 n` (%O 0), and `A246317 n = A246316 (2 ^ n - 1)` (%O 0).
- The phrase *also generate this sequence* is read as: for every listed rule `r` and every `n`, running rule `r` in
  place of Rule 452 from the same single ON cell gives `stage r (2 ^ n - 1)` with exactly `A246317 n` ON cells.
-/

namespace OMA.S_oeis_a246317

/-- The 4 von Neumann neighbours of a cell. -/
def nbrs (p : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)}

/-- One step of the 5-neighbor outer totalistic rule `r` (weights 1 on the cell, 2 on each neighbour): a cell is ON
next iff bit `2 * k + c` of `r` is set, with `c` its own state and `k` its number of ON neighbours. The cells outside
`S` and its neighbours have `c = 0` and `k = 0`; they stay OFF when bit 0 of `r` is clear (see Conventions). -/
def step (r : ℕ) (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  (S ∪ S.biUnion nbrs).filter fun p =>
    Nat.testBit r (2 * (nbrs p ∩ S).card + if p ∈ S then 1 else 0)

/-- The configuration of rule `r` at stage `n`, from a single ON cell at stage 0. -/
def stage (r n : ℕ) : Finset (ℤ × ℤ) :=
  (step r)^[n] {(0, 0)}

/-- A246316: the number of ON cells at stage `n` of Rule 452. -/
def A246316 (n : ℕ) : ℕ :=
  (stage 452 n).card

/-- A246317: `A246316 (2 ^ n - 1)`. -/
def A246317 (n : ℕ) : ℕ :=
  A246316 (2 ^ n - 1)

theorem main :
    ∀ r ∈ ({332, 356, 364, 452, 460, 484, 492, 836, 844, 868, 876, 964, 972, 996, 1004} : Finset ℕ),
      ∀ n : ℕ, (stage r (2 ^ n - 1)).card = A246317 n := by
  sorry

end OMA.S_oeis_a246317
