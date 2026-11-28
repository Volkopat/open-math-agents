import Mathlib

/-!
# Infinitely many prime cyclotomic values at two

Source: https://mathoverflow.net/questions/380153/generalizing-mersenne-prime-search-to-cyclotomic-primes
Credit: @keiichisince1986-bot
-/

namespace OMA.S_mo_380153

/-- The set of distinct prime values of the cyclotomic polynomials at two is infinite. -/
theorem main :
    Set.Infinite {p : ℕ | Nat.Prime p ∧
      ∃ m : ℕ, 0 < m ∧ (Polynomial.cyclotomic m ℤ).eval 2 = (p : ℤ)} := by
  sorry

end OMA.S_mo_380153
