import Mathlib

/-!
# A108411: 3^floor(n/2) counts the subsets S of {0, ..., n} with n not in S + S

Source: https://oeis.org/A108411
Credit: @ivillar

Status: known result. Andrew Howroyd (Nov 20 2021) proved the conjecture: if m pairs of numbers
add up to n, inclusion-exclusion gives 3^m admissible sets, and for even n the element n/2 cannot
be in any of them.

A108411 (offset 0): a(n) = 3^floor(n/2); data 1, 1, 3, 3, 9, 9, 27, 27, 81, ...
Conjecture (Michael Chu, Oct 05 2021): a(n+1) is the number of distinct subsets S of
{0,1,2,...,n} such that the sumset S+S does not contain n.

Formalization notes.
* The subsets of {0, ..., n} are the members of the powerset of Finset.range (n + 1), and the
  sumset S + S = {x + y : x, y in S} is the pointwise sum of finite sets.
* The statement is claimed for every n >= 0.
-/

namespace OMA.S_oeis_a108411

open Pointwise

/-- A108411: a(n) = 3^floor(n/2). -/
def a (n : ℕ) : ℕ := 3 ^ (n / 2)

/-- The subsets S of {0, 1, ..., n} such that the sumset S + S does not contain n. -/
def good (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (n + 1)).powerset.filter (fun S => n ∉ S + S)

/-- Chu's conjecture: a(n+1) is the number of subsets S of {0, ..., n} with n not in S + S. -/
theorem main : ∀ n : ℕ, a (n + 1) = (good n).card := by
  sorry

end OMA.S_oeis_a108411
