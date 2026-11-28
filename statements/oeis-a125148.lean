import Mathlib

/-!
# A125148: a(n) = smallest prime p = z + x, where x is the n-th odd composite number not divisible by 5 and z is a multiple of 10.

Source: https://oeis.org/A125148
Credit: @azmiozgen

Conjecture (from the entry): for every odd (prime or nonprime) number x >= 1 that is not a
multiple of 5 there exists a prime p such that p = z + x, where z is a multiple of 10.

Formalization notes:
* z is taken to be a positive multiple of 10, as in the entry's examples (19 = 10 + 9,
  31 = 10 + 21). This is the stronger reading: with z = 0 allowed, every prime x would be its own
  witness.
* x ranges over the natural numbers x >= 1 that are odd and not divisible by 5.
-/

namespace OMA.S_oeis_a125148

/-- Every odd `x ≥ 1` not divisible by 5 is `p - z` for a prime `p` and a positive multiple `z`
of 10. -/
theorem main :
    ∀ x : ℕ, 1 ≤ x → Odd x → ¬ 5 ∣ x → ∃ p z : ℕ, p.Prime ∧ 0 < z ∧ 10 ∣ z ∧ p = z + x := by
  sorry

end OMA.S_oeis_a125148
