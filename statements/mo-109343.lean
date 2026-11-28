import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Order.Interval.Finset.Nat

/-!
# Optimal Gear Trains

Source: Joseph O'Rourke, https://mathoverflow.net/questions/109343
Credit: @LDJAI

A train is a pair of equally long lists, paired position by position. The first
list drives the second. The empty train represents direct drive at ratio one.
All tooth counts and both entries of the requested ratio are positive. Individual
stages may speed up, and factors may cancel between stages.

For the characterization requested in Q1 and Q2, tabulate one side of the
train at a time. At each length, a state records just the product of the tooth
counts and their total cost. Join two states of equal length by cross
multiplication. Any feasible train supplies a cost cap; a single stage with
counts t*a and t*b always supplies one. The finite recurrence below specifies
an answer independent of minimization over trains.

Q1a asks specifically about four and eight successive 8/32 stages.
Q3 is witnessed by the example suggested by Michael Biro on the source page.
-/

namespace OMA.S_mo_109343

inductive Cost where
  | teeth
  | metal

def weight : Cost → ℕ → ℕ
  | .teeth, x => x
  | .metal, x => x * x

abbrev Train := List ℕ × List ℕ

def sideCost (m : Cost) (xs : List ℕ) : ℕ := (xs.map (weight m)).sum

def cost (m : Cost) (g : Train) : ℕ := sideCost m g.1 + sideCost m g.2

def feasible (t a b : ℕ) (g : Train) : Prop :=
  g.1.length = g.2.length ∧ (∀ x ∈ g.1, t ≤ x) ∧
  (∀ y ∈ g.2, t ≤ y) ∧ b * g.1.prod = a * g.2.prod

def optimal (m : Cost) (t a b : ℕ) (g : Train) : Prop :=
  feasible t a b g ∧ ∀ h, feasible t a b h → cost m g ≤ cost m h

/-- One side, for a fixed number of gears. Coordinates are product and cost. -/
def sideTable (m : Cost) (t cap : ℕ) : ℕ → Finset (ℕ × ℕ)
  | 0 => {(1, 0)}
  | k + 1 =>
    let prev := sideTable m t cap k
    let teeth := (Finset.Icc t cap).filter fun x => weight m x ≤ cap
    ((prev ×ˢ teeth).image fun s => (s.1.1 * s.2, s.1.2 + weight m s.2)).filter
      fun s => s.2 ≤ cap

def costsAt (m : Cost) (t a b cap k : ℕ) : Finset ℕ :=
  let side := sideTable m t cap k
  let pairs := (side ×ˢ side).filter fun s =>
    b * s.1.1 = a * s.2.1 ∧ s.1.2 + s.2.2 ≤ cap
  pairs.image fun s => s.1.2 + s.2.2

/-- The cap is a feasible cost when this function is used in the theorem. -/
def bestCost (m : Cost) (t a b cap : ℕ) : ℕ :=
  let last := cap / (2 * weight m t)
  let values := (Finset.range (last + 1)).biUnion (costsAt m t a b cap)
  (insert cap values).min' (Finset.insert_nonempty _ _)

def quarters (k : ℕ) : Train := (List.replicate k 8, List.replicate k 32)

theorem main :
    (∀ (t a b : ℕ), 0 < t → 0 < a → 0 < b →
      feasible t a b ([t * a], [t * b])) ∧
    (∀ (m : Cost) (t a b : ℕ), 0 < t → 0 < a → 0 < b →
      ∀ seed : Train, feasible t a b seed →
        (∃ g, optimal m t a b g) ∧
        ∀ g, optimal m t a b g ↔
          feasible t a b g ∧ cost m g = bestCost m t a b (cost m seed)) ∧
    (optimal .teeth 8 1 256 (quarters 4) ∧ cost .teeth (quarters 4) = 160) ∧
    (optimal .teeth 8 1 65536 (quarters 8) ∧ cost .teeth (quarters 8) = 320) ∧
    (optimal .teeth 2 1 4 ([2], [8]) ∧ optimal .metal 2 1 4 ([2, 2], [4, 4]) ∧
      ¬ ∃ g, optimal .teeth 2 1 4 g ∧ optimal .metal 2 1 4 g) := by
  sorry

end OMA.S_mo_109343
