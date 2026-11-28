import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Counting sign assignments with sum zero

Source: Sergey Zaitsev, https://mathoverflow.net/questions/282089
Coefficient formula: Fedor Petrov, in the comments on the source question.
Formalization: @YOHSUKE-TAKAHASHI
-/

namespace OMA.S_mo_282089
open Finset Polynomial

/-- Position i represents the integer i+1. Membership specifies a plus sign;
    all other positions carry a minus sign. -/
def weight (s : Finset ℕ) : ℕ := ∑ i ∈ s, (i + 1)

def ways (n : ℕ) : ℕ :=
  (((range n).powerset).filter fun s => weight s = weight (range n \ s)).card

noncomputable def generating (n : ℕ) : ℕ[X] := ∏ i ∈ range n, (1 + X ^ (i + 1))

theorem main : ∀ n : ℕ,
    ways n = if n * (n + 1) / 2 % 2 = 0
             then (generating n).coeff (n * (n + 1) / 4) else 0 := by
  sorry

end OMA.S_mo_282089
