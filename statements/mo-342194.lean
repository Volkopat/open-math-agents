import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace OMA.S_mo_342194

abbrev Point := ℤ × ℤ
abbrev Position := Point → Option Bool

def neighbors (p q : Point) : Prop :=
  (p.1 - q.1).natAbs + (p.2 - q.2).natAbs = 1

def sameColorGraph (position : Position) : SimpleGraph Point :=
  SimpleGraph.fromRel fun p q => neighbors p q ∧ position p = position q

def hasLiberty (position : Position) (p : Point) : Prop :=
  ∃ q r : Point, (sameColorGraph position).Reachable p q ∧
    neighbors q r ∧ position r = none

abbrev AdmissiblePosition :=
  {position : Position // {p : Point | position p ≠ none}.Finite ∧
    ∀ p : Point, position p ≠ none → hasLiberty position p}

/-- Remove all components of the specified color that have no liberty. -/
noncomputable def removeCaptured (position : Position) (color : Bool) : Position := by
  classical
  exact fun p =>
    if position p = some color ∧ ¬ hasLiberty position p then none else position p

/-- Place a stone, remove captured opposing groups, and then remove
captured groups of the placed color. An occupied square leaves the position unchanged. -/
noncomputable def play (color : Bool) (p : Point) (position : Position) : Position :=
  if position p = none then
    let placed := Function.update position p (some color)
    removeCaptured (removeCaptured placed (!color)) color
  else position

abbrev PositionHilbert := ↥(lp (fun _ : AdmissiblePosition => ℂ) 2)

noncomputable def basisVector (position : AdmissiblePosition) : PositionHilbert := by
  classical
  exact lp.single 2 position 1

/-- The bounded placement operators and their adjoints have scalar commutant. -/
theorem main :
    ∃ (move : Bool → Point → AdmissiblePosition → AdmissiblePosition)
      (operators : Bool → Point → (PositionHilbert →L[ℂ] PositionHilbert)),
      (∀ color p position, (move color p position).val = play color p position.val) ∧
      (∀ color p position,
        operators color p (basisVector position) = basisVector (move color p position)) ∧
      ∀ candidate : PositionHilbert →L[ℂ] PositionHilbert,
        (∀ color p, Commute candidate (operators color p) ∧
          Commute candidate (operators color p).adjoint) →
        ∃ scalar : ℂ, candidate = scalar • ContinuousLinearMap.id ℂ PositionHilbert := by
  sorry

end OMA.S_mo_342194
