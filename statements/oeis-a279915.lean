import Mathlib

/-!
# A279915: Numbers m that can be written as x*y with phi(x)*sigma(y) = 2*x*y, where x and y are positive integers, phi(.) is Euler's totient function and sigma(y) is the sum of all positive divisors of y.

Source: https://oeis.org/A279915
Credit: @agchua

The entry is by Zhi-Wei Sun, Dec 22 2016 (offset 1). Two of its comment lines, verbatim:
  Conjecture: (i) All the terms are even. Moreover, if x and y are positive integers with
  phi(x)*sigma(y) = 2*x*y, then y must be even.
  As phi(1) = 1, the sequence contains all perfect numbers, and part (i) of the above
  conjecture implies the well-known conjecture that there are no odd perfect numbers.

Formalisation. phi is Nat.totient and sigma(y) is ArithmeticFunction.sigma 1 y, the sum of the
divisors of y. IsTerm m says that m = x*y for some positive integers x and y with
phi(x)*sigma(y) = 2*x*y, as in the name line. ConjI is part (i) of the conjecture: every term is
even, and y is even in every such solution (x, y). The theorem main states part (i) together
with the two remarks of the second quoted line: every perfect number is a term, and part (i)
implies that there is no odd perfect number. Part (ii) of the conjecture is on a separate comment
line and is not part of this problem.
-/

namespace OMA.S_oeis_a279915

/-- m is a term of A279915: m = x*y with x, y positive and phi(x)*sigma(y) = 2*x*y. -/
def IsTerm (m : ℕ) : Prop :=
  ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ m = x * y ∧
    Nat.totient x * ArithmeticFunction.sigma 1 y = 2 * x * y

/-- Part (i) of the conjecture: all the terms are even, and y must be even. -/
def ConjI : Prop :=
  (∀ m : ℕ, IsTerm m → Even m) ∧
    (∀ x y : ℕ, 0 < x → 0 < y →
      Nat.totient x * ArithmeticFunction.sigma 1 y = 2 * x * y → Even y)

/-- Part (i) of the conjecture, with the remarks that every perfect number is a term and that
part (i) implies that there are no odd perfect numbers. -/
theorem main :
    ConjI ∧ (∀ n : ℕ, Nat.Perfect n → IsTerm n) ∧
      (ConjI → ¬ ∃ n : ℕ, Nat.Perfect n ∧ Odd n) := by
  sorry

end OMA.S_oeis_a279915
