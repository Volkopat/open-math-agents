import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Monoid.WithTop

/-!
# Synchronized processor sessions

Simon Lentner, MathOverflow 124631, March 2013.
Source: https://mathoverflow.net/questions/124631
Formalization: @LDJAI.

Jobs are indivisible and labeled. Each session has the fixed number of processor
queues, and its duration is the largest queue load. An arbitrary finite list of
sessions is allowed, including empty sessions. The question asks, among other
things, for an algorithm. The theorem specifies an exact subset dynamic program
for all nonnegative processing times, including real or rational times.
-/

namespace OMA.S_mo_124631

variable {J T : Type} [DecidableEq J] [AddCommMonoid T] [LinearOrder T]

/-- The queues partition exactly the jobs in S. Empty queues are allowed. -/
def Packs : Finset J → List (Finset J) → Prop
  | S, [] => S = ∅
  | S, Q :: qs => Q ⊆ S ∧ Packs (S \ Q) qs

def duration (w : J → T) : List (Finset J) → T
  | [] => 0
  | Q :: qs => max (∑ j ∈ Q, w j) (duration w qs)

def elapsed (w : J → T) : List (List (Finset J)) → T
  | [] => 0
  | qs :: rest => duration w qs + elapsed w rest

/-- R consists of the jobs left after the first synchronized session. -/
def Legal (w : J → T) (p : ℕ) (W : T) : Finset J → List (List (Finset J)) → Prop
  | S, [] => S = ∅
  | S, qs :: rest =>
    ∃ R ⊆ S, Packs (S \ R) qs ∧ qs.length = p ∧ duration w qs ≤ W ∧ Legal w p W R rest

/-- Minimum duration of one session. The first queue takes Q and the remaining
processors handle its complement. Infinity denotes infeasibility. -/
def oneSession (w : J → T) : ℕ → Finset J → WithTop T
  | 0, S => if S = ∅ then ↑(0 : T) else ⊤
  | p + 1, S => S.powerset.inf fun Q =>
    max ((∑ j ∈ Q, w j : T) : WithTop T) (oneSession w p (S \ Q))

/-- Shortest path on subsets: do the jobs in S minus R in this session, leave
the proper subset R for later, and discard edges that exceed the session cap. -/
def optimum (w : J → T) (p : ℕ) (W : T) (S : Finset J) : WithTop T :=
  if S = ∅ then ↑(0 : T) else
    S.ssubsets.attach.inf fun R =>
      let t := oneSession w p (S \ R.val)
      if t ≤ (W : WithTop T) then t + optimum w p W R.val else ⊤
termination_by S.card
decreasing_by exact Finset.card_lt_card (Finset.mem_ssubsets.mp R.property)

/-- The algorithm detects infeasibility. Every finite answer is attained by a
legal schedule and is a lower bound for every legal schedule. -/
theorem main :
    ∀ (J T : Type) [DecidableEq J] [AddCommMonoid T] [LinearOrder T] [IsOrderedAddMonoid T]
      (S : Finset J) (p : ℕ) (_ : 0 < p) (w : J → T) (W : T)
      (_ : ∀ j ∈ S, 0 ≤ w j) (_ : 0 ≤ W),
      (optimum w p W S = ⊤ ↔ ¬ ∃ plan, Legal w p W S plan) ∧
      ∀ t : T, optimum w p W S = (t : WithTop T) →
        ∃ plan, Legal w p W S plan ∧ elapsed w plan = t ∧
          ∀ other, Legal w p W S other → t ≤ elapsed w other := by
  sorry

end OMA.S_mo_124631
