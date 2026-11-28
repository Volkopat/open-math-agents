import Mathlib

/-!
# Layman’s divisor-power congruences for OEIS A196226

Source: https://oeis.org/A196226 (OEIS Foundation, CC BY-SA 4.0)
Credit: @konradsiebor

The entry gives three explicit conjectures for divisor powers 2, 3, and 4.
Membership uses exact division by two, as in the source program, so the
membership predicate explicitly requires an even input. The later OEIS
comment suggests other congruences without specifying cutoffs.

A simultaneous counterexample at 690 is reported by the Omega Institute.
https://the-omega-institute.github.io/trureturing-mdbook/Problems/oeis-a196226-layman-divisor-power-congruence-refutation.html
-/

namespace OMA.S_oeis_a196226

open ArithmeticFunction

/-- The sum of the divisors of `m`, reduced modulo `m`, equals `3 + m / 2`. -/
def IsTerm (m : ℕ) : Prop := 2 ∣ m ∧ sigma 1 m % m = 3 + m / 2

/-- Layman’s three congruences with the cutoffs given in A196226. -/
theorem main :
    (∀ m : ℕ, 14 ≤ m → IsTerm m → sigma 2 m ≡ 5 + m / 2 [MOD m]) ∧
    (∀ m : ℕ, 22 ≤ m → IsTerm m → sigma 3 m ≡ 9 + m / 2 [MOD m]) ∧
    (∀ m : ℕ, 38 ≤ m → IsTerm m → sigma 4 m ≡ 17 + m / 2 [MOD m]) := by
  sorry

end OMA.S_oeis_a196226
