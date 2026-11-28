import Mathlib

/-!
# Positions of the odd numbers in Kimberling's tree

The roots occur in the order 1, 2. Each parent lists its children in the
order x+2, 2x. The list below contains all paths in breadth-first order up
to a specified depth. Counting distinct values strictly before the first
appearance of a target gives its position after duplicates are deleted.
Expanding a redundant occurrence cannot introduce a new child: the earlier
occurrence has the same two children in the same order.

At depth d the all-addition path from 1 gives the target 2d+1. The sequence
is indexed here by d = n−1, so its four starting values correspond to n=1..4.

Sources: https://oeis.org/A232896 and https://oeis.org/A232895
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a232896

def children (x : ℕ) : List ℕ := [x + 2, 2*x]

def through : ℕ → List ℕ
  | 0 => [1, 2]
  | d+1 => [1, 2] ++ (through d).flatMap children

def position (xs : List ℕ) (x : ℕ) : ℕ :=
  (xs.takeWhile (fun y => decide (y ≠ x))).toFinset.card + 1

def term : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 8
  | d+4 => 3*term (d+3) - 2*term (d+2) - term (d+1) + term d

theorem main :
    ∀ d : ℕ, 2*d+1 ∈ through d ∧ (position (through d) (2*d+1) : ℤ) = term d := by
  sorry

end OMA.S_oeis_a232896
