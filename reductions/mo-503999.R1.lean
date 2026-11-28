import OMAStatements.S_mo_503999

-- Reduction mo-503999.R1 of Is 1001 the only palindrome which is a product of three consecutive primes?
-- Credit: @futurum-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Idea: a decimal palindrome with an even number of digits is divisible by 11, because
-- 10 = -1 (mod 11) and the alternating digit sum of an even-length palindrome cancels in pairs
-- (Mathlib's `Nat.eleven_dvd_of_palindrome`). So a palindromic product of three consecutive
-- primes either has 11 as a factor (H1: then the primes are among 5, 7, 11, 13, 17 and only
-- 7 * 11 * 13 = 1001 is a palindrome) or has an odd number of digits and is prime to 11 (H2,
-- the open core).

namespace OMA.R_mo_503999_R1

open OMA.S_mo_503999

/-- The product contains the factor 11: only `7 * 11 * 13 = 1001` is a palindrome. -/
def H1 : Prop := ∀ i : ℕ,
    IsPalindrome (Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) * Nat.nth Nat.Prime (i + 2)) →
    11 ∣ Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) * Nat.nth Nat.Prime (i + 2) →
      Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) * Nat.nth Nat.Prime (i + 2) = 1001

/-- The open core: an odd number of digits and no factor 11. -/
def H2 : Prop := ∀ i : ℕ,
    IsPalindrome (Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) * Nat.nth Nat.Prime (i + 2)) →
    Odd (Nat.digits 10
      (Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) * Nat.nth Nat.Prime (i + 2))).length →
    ¬ 11 ∣ Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) * Nat.nth Nat.Prime (i + 2) →
      Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) * Nat.nth Nat.Prime (i + 2) = 1001

theorem main : H1 → H2 → type_of% @OMA.S_mo_503999.main := by
  intro h1 h2 i hpal
  by_cases h11 : 11 ∣ Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) * Nat.nth Nat.Prime (i + 2)
  · exact h1 i hpal h11
  · refine h2 i hpal ?_ h11
    rcases Nat.even_or_odd (Nat.digits 10
      (Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) * Nat.nth Nat.Prime (i + 2))).length with
      he | ho
    · exact absurd (Nat.eleven_dvd_of_palindrome (List.Palindrome.of_reverse_eq hpal) he) h11
    · exact ho

end OMA.R_mo_503999_R1
