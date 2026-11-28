import Mathlib

/-!
# A080149: numbers k with k^2 + 1 and k^2 + 3 both prime

Source: https://oeis.org/A080149
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A080/A080149.seq
Credit: @Bondyboy2001

The sequence consists of positive integers `k` such that `k^2 + 1` and `k^2 + 3` are both
prime. Hardy and Littlewood conjectured that this sequence is infinite.

A separate OEIS formula comment says that `a(n)` is asymptotic to `c*n*log(n)^2` with `c`
only described as around `2.9`; since no exact constant is given, that imprecise asymptotic
statement is not the theorem formalized here.
-/

namespace OMA.S_oeis_a080149

/-- Membership in A080149. -/
def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ (k ^ 2 + 1).Prime ∧ (k ^ 2 + 3).Prime

theorem main : {k : ℕ | IsTerm k}.Infinite := by
  sorry

end OMA.S_oeis_a080149
