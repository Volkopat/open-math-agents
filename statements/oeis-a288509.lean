import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Positions of 0 in the even limiting word of A288508

Clark Kimberling, June 12, 2017. Source: https://oeis.org/A288509
Credit: @Aryan-Poonacha

The left-to-right rewrite and initial word agree with the merged A288511
statement (https://github.com/lefttosolve2/open-math-agents/pull/19590).
Positions and occurrence numbers start at one.
At position p the letter is 0, and exactly n such letters occur in the first
p places. Requiring this eventually along the even iterates specifies the
n-th occurrence in the limiting word. The two rational endpoints express
the source's displayed decimal prefix as a half-open interval.
-/

namespace OMA.S_oeis_a288509

open Filter Topology

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, true, false, true] ++ rewrite w
  | true :: false :: w => [false, false, true] ++ rewrite w
  | false :: true :: w => false :: rewrite (true :: w)
  | true :: true :: w => true :: rewrite (true :: w)
termination_by w => w.length

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

/-- The p-th letter is b, and is the n-th occurrence of b in this finite word. -/
def IsPosition (b : Bool) (w : List Bool) (n p : ℕ) : Prop :=
  0 < p ∧ w[p-1]? = some b ∧ (w.take p).count b = n

theorem main :
    ∃ a : ℕ → ℕ, (∀ n : ℕ, 1 ≤ n →
      ∀ᶠ t : ℕ in atTop, IsPosition false (word (2*t)) n (a n)) ∧
    ∃ m : ℝ, 152/100 ≤ m ∧ m < 153/100 ∧
      Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 m) ∧
      ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ)/n ∧ m - (a n : ℝ)/n < 1 := by
  sorry

end OMA.S_oeis_a288509
