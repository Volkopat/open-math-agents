import Mathlib

/-!
# Greatest term of OEIS A250404

Jaroslav Krizek conjectured that the greatest positive integer k for which
the set of totients of divisors of k is the set of proper divisors of k+1 is
4294967295. A repeated totient contributes just one element to the image.

Source: https://oeis.org/A250404
-/

namespace OMA.S_oeis_a250404

def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ k.divisors.image Nat.totient = (k + 1).properDivisors

theorem main : IsGreatest {k : ℕ | IsTerm k} 4294967295 := by
  sorry

end OMA.S_oeis_a250404
