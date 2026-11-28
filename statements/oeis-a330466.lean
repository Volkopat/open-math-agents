import Mathlib

/-!
# The gap-two partition row sums of A330466

For a given n and k there is at most one partition of n into k positive
parts with successive difference two. The triangle counts the number of
parts in this partition, or zero when it does not exist. Starting from
the positive first part a+1, the part at index j is a+1+2j.

The conjectured row sum is A066839, the sum of divisors no larger than
the square root of n. Omar E. Pol proposed this interpretation.
In December 2020 N. J. A. Sloane verified it via the generating
function recorded by Michael Somos in A066839.
Sources: https://oeis.org/A330466 and https://oeis.org/A066839
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a330466
open Finset

def partitionTotal (a k : ℕ) : ℕ := ∑ j ∈ range k, (a+1+2*j)

noncomputable def rowEntry (n k : ℕ) : ℕ := by
  classical
  exact if ∃ a : ℕ, partitionTotal a k = n then k else 0

theorem main : ∀ n : ℕ, 0<n → ∑ k ∈ range (n+1), rowEntry n k =
    ∑ k ∈ n.divisors.filter (fun d => d≤n.sqrt), k := by
  sorry

end OMA.S_oeis_a330466
