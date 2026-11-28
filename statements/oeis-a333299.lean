import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# OEIS A333299: canonical quarter-turn sequences

Source: https://oeis.org/A333299
Credit: @etaubman
The formulas were conjectured by Colin Barker (2020) and confirmed by
Ben Whitmore (2024); this file formalizes the known result.

A move has one of three axes and one of four quarter turns: positive or
negative on the first or second face of that axis. Opposite faces commute;
within each maximal same-axis block the first face precedes the second.
A face power is represented by the empty word, a positive quarter turn,
a negative quarter turn, or two positive quarter turns. The latter is the
chosen unique representation of a half turn. These are precisely the
canonical sequences counted in Rokicki's Table 9.5.

The four live states record first-face positive single, first-face closed,
second-face positive single, and second-face closed. Closed means either a
negative single or a half turn; these have identical legal continuations.
The axis is retained explicitly. `next` checks the exact next quarter turn;
`a` counts accepted words of length n over the twelve actual moves. It is
not defined from a proposed recurrence or generating function.
-/

namespace OMA.S_oeis_a333299

open Finset

abbrev Move := Fin 3 × Fin 4
abbrev State := Option Move

def localNext (s m : Fin 4) : Option (Fin 4) :=
  if s.val = 0 ∧ m.val = 0 then some 1
  else if (s.val = 0 ∨ s.val = 1) ∧ m.val = 2 then some 2
  else if (s.val = 0 ∨ s.val = 1) ∧ m.val = 3 then some 3
  else if s.val = 2 ∧ m.val = 2 then some 3
  else none

def next : State → Move → State
  | none, _ => none
  | some (ax, s), (bx, m) =>
      if ax.val = bx.val then (localNext s m).map (fun t => (ax, t)) else some (bx, m)

def run (l : List Move) (s : State) : State := l.foldl next s

def canonical : List Move → Prop
  | [] => True
  | m :: ms => run ms (some m) ≠ none

instance (l : List Move) : Decidable (canonical l) := by
  cases l <;> unfold canonical <;> infer_instance

def a (n : ℕ) : ℚ :=
  ∑ w : Fin n → Move, if canonical (List.ofFn w) then 1 else 0

def generatingFunction : PowerSeries ℚ := PowerSeries.mk a

noncomputable def denominator : PowerSeries ℚ :=
  1 - 8 * PowerSeries.X - 12 * PowerSeries.X^2 - 8 * PowerSeries.X^3 - 2 * PowerSeries.X^4

theorem main :
    generatingFunction = (1 + PowerSeries.X)^4 * denominator⁻¹ ∧
    ∀ n : ℕ, 4 < n → a n = 8*a (n-1) + 12*a (n-2) + 8*a (n-3) + 2*a (n-4) := by
  sorry

end OMA.S_oeis_a333299
