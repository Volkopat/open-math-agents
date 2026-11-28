import Mathlib

/-!
# A173527: a(n) = 1 + A053828(n-1), where A053828 is the sum of digits in base 7

Source: https://oeis.org/A173527
Credit: @xor2k

Formalizes the OEIS A173527 conjecture (Joerg Arndt): the sequence is the fixed point of the
morphism 1->{1,2,3,...b}, 2->{2,3,4...,b+1}, j->{j,j+1,...,j+b-1} for b=7.

Conventions:
* Offset 1: `a n = 1 + (sum of the base-7 digits of n - 1)` for `n ≥ 1`, using `Nat.digits 7`.
* The morphism is `phi j = [j, j+1, ..., j+6]`, extended to words by concatenation
  (`List.flatMap phi`).
* Being the fixed point (the infinite word `a 1, a 2, a 3, ...` with first letter 1 that equals
  its own image) is stated as: `a 1 = 1`, and for every `N` the image of the length-`N` prefix
  `[a 1, ..., a N]` is the length-`7 N` prefix `[a 1, ..., a (7 N)]`. Since every block has
  length 7, this is exactly the statement that the image of the infinite word is the word itself.
-/

namespace OMA.S_oeis_a173527

/-- `a(n) = 1 + A053828(n-1)`, the base-7 digit sum of `n - 1` plus one (offset 1). -/
def a (n : ℕ) : ℕ :=
  1 + (Nat.digits 7 (n - 1)).sum

/-- The morphism `j ↦ [j, j+1, ..., j+6]` (the case `b = 7`). -/
def phi (j : ℕ) : List ℕ :=
  (List.range 7).map (fun i => j + i)

/-- `a` is the fixed point of `phi` starting with the letter 1. -/
theorem main :
    a 1 = 1 ∧ ∀ N : ℕ,
      ((List.range N).map (fun m => a (m + 1))).flatMap phi =
        (List.range (7 * N)).map (fun k => a (k + 1)) := by
  sorry

end OMA.S_oeis_a173527
