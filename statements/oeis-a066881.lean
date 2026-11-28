import Mathlib

/-!
# A066881: Numbers k such that sigma(phi(k))/sigma(k) is an integer >= 4.

Source: https://oeis.org/A066881
Credit: @azmiozgen

Conjecture (from the entry): all natural numbers 1,2,3,...,n will eventually occur among the
integer values of sigma(phi(k))/sigma(k).

Formalization notes:
* "m occurs as an integer value of sigma(phi(k))/sigma(k)" is stated without division as
  sigma(phi(k)) = m * sigma(k), for some k >= 1 (k = 0 is excluded: there sigma(0) = 0 in Mathlib).
* The conjecture is stated for every m >= 1.
* Controls: k = 1 gives the value 1; for the first term k = 121679, sigma(phi(k)) = 489600 and
  sigma(k) = 122400, value 4, as in the entry's example.
-/

namespace OMA.S_oeis_a066881

open ArithmeticFunction

/-- Every positive integer is a value of `σ(φ(k)) / σ(k)` for some `k ≥ 1`. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ∃ k : ℕ, 1 ≤ k ∧ sigma 1 (Nat.totient k) = m * sigma 1 k := by
  sorry

end OMA.S_oeis_a066881
