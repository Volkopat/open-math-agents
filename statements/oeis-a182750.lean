import Mathlib

/-!
# A182750: a(n) = the largest multiple of n with n digits and exactly n divisors; a(n) = 0 if no such number exists.

Source: https://oeis.org/A182750
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A182750 (Jaroslav Krizek, Nov 27 2010): a(n) > 0 for
all nonsquarefree n except for n = 4.

Conventions:
* The sequence has offset 1 (data 1, 0, 0, 0, 0, 0, 0, 99999992, 998117649, 0, 25937424601,
  999999999924, ...).
* a(n) is the largest multiple of n with n digits and exactly n divisors, and a(n) = 0 if no such
  number exists; so a(n) > 0 says exactly that some multiple of n has n decimal digits and exactly
  n divisors (there are finitely many n-digit numbers, so a largest one then exists).
* The number of decimal digits of m is the length of `Nat.digits 10 m`; the number of divisors is
  the cardinality of `Nat.divisors m`.
* n ranges over the positive integers (the offset is 1); `nonsquarefree` is the negation of the
  Mathlib predicate `Squarefree`.
-/

namespace OMA.S_oeis_a182750

/-- The conjecture recorded in A182750: for every nonsquarefree n other than 4 there is a multiple
of n with n digits and exactly n divisors. -/
theorem main : ∀ n : ℕ, 0 < n → ¬Squarefree n → n ≠ 4 →
    ∃ m : ℕ, n ∣ m ∧ (Nat.digits 10 m).length = n ∧ m.divisors.card = n := by
  sorry

end OMA.S_oeis_a182750
