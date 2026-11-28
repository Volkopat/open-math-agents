import Mathlib

/-!
# A135953: (Nonprime Fibonacci numbers with prime indices) that have exactly 2 prime factors

Source: https://oeis.org/A135953
Credit: @xor2k

Formalizes the OEIS A135953 conjecture: All numbers in this sequence are products of two sums of
two squares, e.g. 4181 = 37*113 = (1^2+6^2)*(7^2+8^2), 1346269 = 557*2417 = (14^2+19^2)*(4^2+49^2).

Conventions: `m` is a term iff `m = F(p)` (`F = Nat.fib`) for a prime `p`, `m` is not prime, and
`m` has exactly 2 prime factors counted with multiplicity (`ArithmeticFunction.cardFactors m = 2`,
i.e. `m` is a semiprime; this reproduces the OEIS data). Since every sum of two squares is trivially
such a product with second factor `1 = 1^2 + 0^2`, the claim is read as in the examples: `m` is a
product of two sums of two squares that are both greater than `1`. As `m` is a semiprime, these two
factors are then exactly the two prime factors of `m`, matching the examples.
-/

namespace OMA.S_oeis_a135953

/-- `m` is a term of A135953: a nonprime Fibonacci number with prime index having exactly two
prime factors (with multiplicity). -/
def IsTerm (m : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ m = Nat.fib p ∧ ¬ m.Prime ∧ ArithmeticFunction.cardFactors m = 2

/-- Every term is a product of two sums of two squares, both factors greater than `1`. -/
theorem main :
    ∀ m : ℕ, IsTerm m →
      ∃ a b c d : ℕ, m = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) ∧ 1 < a ^ 2 + b ^ 2 ∧
        1 < c ^ 2 + d ^ 2 := by
  sorry

end OMA.S_oeis_a135953
