import Mathlib

/-!
# A231897: a(n) = smallest m such that wt(m^2) = n (where wt(i) = A000120(i)), or -1 if no such m exists.

Source: https://oeis.org/A231897
Credit: @luciusacarr

Data: 0, 1, 3, 5, 13, 11, 21, 39, 45, 75, 155, 217, 331, 181, 627, 923, ... (offset 0).

The entry's comment: Conjecture: a(n) is never -1. (It seems likely that the arguments of
Lindström (1997) could be modified to establish this conjecture.) `main` states that conjecture.

Reading of the source:
* `wt(i)` (A000120) is the binary weight of `i`, the number of 1's in its binary expansion, which
  is the sum of its base-2 digits `(Nat.digits 2 i).sum`.
* `a(n)` is never -1 means: for every `n ≥ 0` (the offset is 0) some `m ≥ 0` has `wt(m^2) = n`.
-/

namespace OMA.S_oeis_a231897

/-- A000120: the binary weight of `i`. -/
def wt (i : ℕ) : ℕ := (Nat.digits 2 i).sum

theorem main :
    -- a(n) is never -1: every n ≥ 0 is the binary weight of some square.
    ∀ n : ℕ, ∃ m : ℕ, wt (m ^ 2) = n := by
  sorry

end OMA.S_oeis_a231897
