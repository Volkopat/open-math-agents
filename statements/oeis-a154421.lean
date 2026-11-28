import Mathlib

/-!
# A154421: Number of ways to express n as the sum of an odd prime, a positive Fibonacci number and an even Lucas number.

Source: https://oeis.org/A154421
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, Jan 09 2009): a(n) > 0 for all n = 6, 7, ...; in other words, any integer
n > 5 can be written in the form p + F_s + L_{3t} with p an odd prime, s positive and t nonnegative.

Formalization notes:
* F_s = `Nat.fib s`; L_k is the k-th Lucas number (L_0 = 2, L_1 = 1), defined below; the even Lucas
  numbers are the L_{3t}.
* a(n) > 0 means n has at least one representation, so the conjecture is stated as the existence
  of a representation.
* Controls (computed): every n with 6 ≤ n < 3000 has a representation.
-/

namespace OMA.S_oeis_a154421

/-- The Lucas numbers `L(0) = 2, L(1) = 1, L(n+2) = L(n+1) + L(n)`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 6 ≤ n → ∃ p s t : ℕ, p.Prime ∧ Odd p ∧ 0 < s ∧ p + Nat.fib s + lucas (3 * t) = n := by
  sorry

end OMA.S_oeis_a154421
