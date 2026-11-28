import Mathlib

/-!
# A154258: Number of triples <p,s,t> such that p+F_s+(F_t)^2=n, where p is an odd prime, s and t are greater than one and the Fibonacci number F_s or F_t is odd.

Source: https://oeis.org/A154258
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun): a(n) > 0 for all n = 5, 6, ... (any integer n > 4 can be written as the
sum of an odd prime, a positive Fibonacci number and a square of a positive Fibonacci number, with
one of the two Fibonacci numbers odd).

Formalization notes:
* F_s = `Nat.fib s`.
* a(n) > 0 means n has at least one representation, so the conjecture is stated as the existence
  of a representation.
* Controls (computed): every n with 5 ≤ n < 3000 has a representation.
-/

namespace OMA.S_oeis_a154258



/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 5 ≤ n → ∃ p s t : ℕ, p.Prime ∧ Odd p ∧ 1 < s ∧ 1 < t ∧
      (Odd (Nat.fib s) ∨ Odd (Nat.fib t)) ∧ p + Nat.fib s + Nat.fib t ^ 2 = n := by
  sorry

end OMA.S_oeis_a154258
