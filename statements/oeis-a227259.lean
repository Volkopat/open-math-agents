import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.IntervalCases

/-!
# OEIS A227259: threshold images of lexicographically ordered binary arrays

Source: https://oeis.org/A227259
Credit: @etaubman

A source row is a binary word of length three, encoded by Fin 8 using the
explicit table below. `rowsOrdered` and `columnsOrdered` compare the full
parent rows and columns lexicographically, in the source's nondecreasing
order. Each output row is a two-bit word encoded as high bit plus low bit:
the left bit contributes two, and the right bit contributes one. A bit is
one exactly when its adjacent 2 by 2 parent block has sum at most two.
`arrayCount` counts distinct output words by existence of a valid parent;
it does not count parents. Ternary words have entries zero, one, or two.

The source has offset n=1. The auxiliary arrayCount 0 is well-defined,
but the stated generating series starts at one and has constant term zero.
-/

namespace OMA.S_oeis_a227259

abbrev Row := Fin 8
abbrev Symbol := Fin 4

def bits (r : Row) (j : Fin 3) : Fin 2 :=
  ![![0,0,0],
  ![0,0,1],
  ![0,1,0],
  ![0,1,1],
  ![1,0,0],
  ![1,0,1],
  ![1,1,0],
  ![1,1,1]] r j

/-- Non-strict lexicographic order on finite lists. -/
def lexLE : List ℕ → List ℕ → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x < y ∨ (x = y ∧ lexLE xs ys)

def column (rs : List Row) (j : Fin 3) : List ℕ :=
  rs.map (fun r => (bits r j).val)

def rowLex (r s : Row) : Prop :=
  lexLE [↑(bits r 0), ↑(bits r 1), ↑(bits r 2)]
    [↑(bits s 0), ↑(bits s 1), ↑(bits s 2)]

def rowsOrdered : List Row → Prop
  | r :: s :: rs => rowLex r s ∧ rowsOrdered (s :: rs)
  | _ => True

def columnsOrdered (rs : List Row) : Prop :=
  lexLE (column rs 0) (column rs 1) ∧
  lexLE (column rs 1) (column rs 2)

def label (r s : Row) : Symbol :=
  (if (bits r 0).val + (bits r 1).val + (bits s 0).val + (bits s 1).val ≤ 2
    then 2 else 0) +
  (if (bits r 1).val + (bits r 2).val + (bits s 1).val + (bits s 2).val ≤ 2
    then 1 else 0)

def thresholds : List Row → List Symbol
  | r :: s :: rs => label r s :: thresholds (s :: rs)
  | _ => []

def actualImage (w : List Symbol) : Prop :=
  ∃ rs : List Row, rs.length = w.length + 1 ∧ rowsOrdered rs ∧
    columnsOrdered rs ∧ thresholds rs = w

noncomputable def arrayCount (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n → Symbol)).filter
    (fun w => actualImage (List.ofFn w))).card

def ternaryCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin 3 => (∑ i, (w i).val) ≤ 4)).card

/-- The source sequence starts at n=1; the series therefore has constant term zero. -/
noncomputable def generatingSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (arrayCount n : ℚ))

theorem main :
    (∀ n : ℕ, 1 ≤ n → arrayCount n = ternaryCount n) ∧
    generatingSeries =
      (PowerSeries.X * (3 - 6*PowerSeries.X + 8*PowerSeries.X^2 -
        5*PowerSeries.X^3 + PowerSeries.X^4)) * ((1 - PowerSeries.X)^5)⁻¹ := by
  sorry

end OMA.S_oeis_a227259
