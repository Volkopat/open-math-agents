import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.Divisors

/-!
# Sums of heads of 2-dense divisor blocks

A379379 sums the odd divisors d for which no other divisor j satisfies
j<d<2j. The geometric blocks are the actual maximal runs of sorted
divisors with consecutive ratio at most two. For the adjacent-pair
formulas use predecessor zero at the first divisor, so that 1 is counted
as the first head, in accordance with the published values.

Sources: https://oeis.org/A379379, https://oeis.org/A383147,
https://oeis.org/A389591, https://oeis.org/A000593 and https://oeis.org/A000203
(OEIS Foundation, CC BY-SA 4.0). Credit: @Solitude1312
-/

namespace OMA.S_oeis_a379379

def eligible (D : Finset ℕ) (d : ℕ) : Prop := Odd d ∧ ∀ j ∈ D, j < d → 2*j ≤ d

def excluded (D : Finset ℕ) (d : ℕ) : Prop := Odd d ∧ ∃ j ∈ D, j < d ∧ d < 2*j

noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact (n.divisors.sort.filter fun d => decide (eligible n.divisors d)).sum

def blockSum (n : ℕ) : ℕ :=
  ((n.divisors.sort.splitBy (fun d e => decide (e ≤ 2*d))).map (fun r => r.headD 0)).sum

def adjacentSum (test : ℕ → ℕ → Bool) (previous : ℕ) (xs : List ℕ) : ℕ :=
  ((((previous :: xs).zip xs).filter (fun p => test p.1 p.2)).map Prod.snd).sum

def oddSum (n : ℕ) : ℕ := (n.divisors.sort.filter fun d => decide (Odd d)).sum

noncomputable def excludedSum (n : ℕ) : ℕ := by
  classical
  exact (n.divisors.sort.filter fun d => decide (excluded n.divisors d)).sum

theorem main : ∀ n : ℕ, 0 < n →
    a n = blockSum n ∧
    a n = adjacentSum (fun b d => decide (2*b < d)) 0 n.divisors.sort ∧
    a n = oddSum n - excludedSum n ∧
    a n = n.divisors.sort.sum - adjacentSum (fun b d => decide (d ≤ 2*b)) 0 n.divisors.sort := by
  sorry

end OMA.S_oeis_a379379
