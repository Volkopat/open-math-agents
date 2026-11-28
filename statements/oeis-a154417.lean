import Mathlib

/-!
# A154417: Number of ways to express n as the sum of an odd prime, a positive Fibonacci number and half of a positive Fibonacci number.

Source: https://oeis.org/A154417
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, Jan 09 2009): a(n) > 0 for every n = 5, 6, ...; in other words, any
integer n > 4 can be written in the form p + F_s + F_{3t}/2 with p an odd prime and s, t > 0.

Formalization notes:
* F_s = `Nat.fib s`; F_{3t} is even, so F_{3t}/2 is exact in ℕ.
* a(n) > 0 means n has at least one representation, so the conjecture is stated as the existence
  of a representation.
* Controls (computed): every n with 5 ≤ n < 3000 has a representation.
-/

namespace OMA.S_oeis_a154417



/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 5 ≤ n → ∃ p s t : ℕ, p.Prime ∧ Odd p ∧ 0 < s ∧ 0 < t ∧
      p + Nat.fib s + Nat.fib (3 * t) / 2 = n := by
  sorry

end OMA.S_oeis_a154417
