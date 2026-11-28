import Mathlib

/-!
# A208354: compositions with one possible even part or one run of ones

Source: https://oeis.org/A208354
Credit: @rgoldman73-dev

This is Gregory L. Simay's September 29, 2018 conjecture. Both sides count
compositions of n (ordered lists of positive integers summing to n).

`completions r k` enumerates the compositions of r+k whose first part is at
least k. At each of the r remaining units, either extend the current part,
or finish it and start a new part. For positive k this enumerates each such
composition exactly once. `compositions 0` contains just the empty list.

The left predicate literally counts the even parts. The right predicate
scans the parts in three phases: 0 before the run of ones, 1 inside that
run, and 2 after it. A 1 in phase 2 is rejected. A composition without any
ones is allowed, as is the empty composition. The phase is initially 0.
Thus the right side permits exactly the patterns (not 1)* 1* (not 1)*.
-/

namespace OMA.S_oeis_a208354

def completions : ℕ → ℕ → List (List ℕ)
  | 0, k => [[k]]
  | r+1, k => completions r (k+1) ++ (completions r 1).map (k :: ·)

def compositions : ℕ → List (List ℕ)
  | 0 => [[]]
  | n+1 => completions n 1

def atMostOneEven (l : List ℕ) : Bool :=
  decide ((l.filter (fun k => k % 2 == 0)).length ≤ 1)

def oneRun : ℕ → List ℕ → Bool
  | _, [] => true
  | phase, k :: l =>
      if k = 1 then
        if phase = 2 then false else oneRun 1 l
      else oneRun (if phase = 1 then 2 else phase) l

def a (n : ℕ) : ℕ := ((compositions n).filter atMostOneEven).length
def b (n : ℕ) : ℕ := ((compositions n).filter (oneRun 0)).length

theorem main : ∀ n : ℕ, a n = b n := by
  sorry

end OMA.S_oeis_a208354
