import Mathlib

/-!
# Cost of the divide-and-conquer Fibonacci evaluation (OEIS A331124)

The zeroth, first and second Fibonacci values each take one evaluation.
An odd argument takes one evaluation plus the two calls at the half-index
and its successor. An even argument takes one plus three calls centered
at its half-index. The count includes each call as in the OEIS definition.

The source conjectures a constant multiple of n^(4/3) as an eventual
upper bound. No numerical constant is specified in the entry.
Source: https://oeis.org/A331124
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a331124

def calls (n : ℕ) : ℕ :=
  if h : n ≤ 2 then 1
  else if n%2=0 then 1+calls (n/2-1)+calls (n/2)+calls (n/2+1)
  else 1+calls (n/2)+calls (n/2+1)
termination_by n
decreasing_by all_goals omega

theorem main :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (calls n : ℝ) ≤ C*(n : ℝ)^((4:ℝ)/3) := by
  sorry

end OMA.S_oeis_a331124
