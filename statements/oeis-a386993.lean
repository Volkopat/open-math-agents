import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.Divisors

/-!
# Dense divisor blocks at squarefree numbers

A386993 splits the sorted divisors at every increase by a factor greater
than two. For A237271 we use Hartmut F. W. Hoft's proved characterization
as the length of row n of A379288: count odd divisors d for which there
is no divisor j with j < d < 2j. The two sides use independent definitions.
The stronger all-integer block identity also appeared in the 2026
AlphaProof Nexus results for A237271.

Sources: https://oeis.org/A386993, https://oeis.org/A237271 and
https://oeis.org/A379288 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a386993

/-- Count actual maximal runs of adjacent divisors with ratio at most two. -/
def blockCount (n : ℕ) : ℕ :=
  (n.divisors.sort.splitBy (fun d e => decide (e ≤ 2 * d))).length

/-- Number of parts in the symmetric representation of sigma(n), by Hoft's
characterization of the entries of row n of A379288. -/
def sigmaParts (n : ℕ) : ℕ :=
  n.divisors.sort.countP fun d =>
    decide (Odd d ∧ ∀ j ∈ n.divisors, j < d → 2 * j ≤ d)

/-- Nat.nth counts from zero, so index k selects the (k+1)st squarefree number. -/
theorem main : ∀ k : ℕ, let n := Nat.nth (Squarefree : ℕ → Prop) k
    blockCount n = sigmaParts n := by
  sorry

end OMA.S_oeis_a386993
