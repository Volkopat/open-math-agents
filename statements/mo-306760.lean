import Mathlib

/-!
# MO 306760: nonunitary perfect numbers

Source: https://mathoverflow.net/questions/306760

A divisor d of n is nonunitary when d and n/d are not coprime.  The question asks
whether every positive n whose nonunitary divisors sum to n is four times an even
perfect number.  The example given there is 24 = 4 * 6.  Only the body of `main`
is `sorry`; all definitions below are complete.
-/

namespace OMA.S_mo_306760

/-- Sum of the nonunitary divisors of a positive integer. -/
def nonunitaryDivisorSum (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors.filter (fun d => ¬ Nat.Coprime d (n / d)), d

theorem main :
    ∀ n : ℕ, 0 < n → nonunitaryDivisorSum n = n →
      ∃ k : ℕ, n = 4 * k ∧ Nat.Perfect k ∧ Even k := by
  sorry

end OMA.S_mo_306760
