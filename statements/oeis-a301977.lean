import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# OEIS A301977

Rémy Sigrist's sequence counts distinct positive integers obtainable by
retaining a subsequence of the binary digits of n. On July 4, 2019,
Ilya Gutkovskiy conjectured a formula using Stirling numbers of the second
kind.

Source: https://oeis.org/A301977
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a301977

/-- A final binary digit can be discarded or appended to any previously
obtainable numeral. A finite set counts each resulting value once. -/
def appendDigit (S : Finset Nat) (b : Nat) : Finset Nat :=
  S ∪ S.image (fun x => 2*x+b)

/-- Include the value zero for the empty subsequence. Leading zeroes do
not change a value, so deleting zero at the end leaves exactly the
positive integers whose canonical binary expansion is a subsequence. -/
def subseqs (n : Nat) : Finset Nat :=
  if n = 0 then {0} else appendDigit (subseqs (n/2)) (n%2)
termination_by n
decreasing_by omega

theorem main : ∀ n : Nat, 0 < n →
    (subseqs n).card - 1 =
      ∑ k ∈ Finset.range n, Nat.stirlingSecond (n+1) (k+1) % 2 := by
  sorry

end OMA.S_oeis_a301977
