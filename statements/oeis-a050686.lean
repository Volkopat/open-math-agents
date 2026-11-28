import Mathlib

/-!
# A050686: Number of palindromes of length n and containing the digit 1 (or any other fixed
nonzero digit).

Source: https://oeis.org/A050686
Credit: @bnb9001

a(n) counts the n-digit decimal palindromes (no leading zero) that contain the digit 1
(offset 1: 1, 1, 18, 18, 252, 252, 3168, ...).

Conjecture (Colin Barker, empirical g.f.): -x*(x-1)*(x+1)^2 / ((3*x-1)*(3*x+1)*(10*x^2-1)). Sela Fried
notes that the conjectured g.f. is correct, equivalently a(n) = 9*10^(n/2 - 1) - 8*9^(n/2 - 1) for n
even and a(n) = 9*10^((n-1)/2) - 8*9^((n-1)/2) for n odd. Both cases are the closed form below, with
(n+1)/2 - 1 (natural division) equal to n/2 - 1 for even n and (n-1)/2 for odd n.
-/

namespace OMA.S_oeis_a050686

open Finset

/-- `k` is a decimal palindrome. -/
def IsPal (k : ℕ) : Prop := (Nat.digits 10 k).reverse = Nat.digits 10 k

open Classical in
/-- A050686: the number of `n`-digit palindromes containing the digit 1. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Ico (10 ^ (n - 1)) (10 ^ n)).filter fun k => IsPal k ∧ 1 ∈ Nat.digits 10 k).card

/-- The conjectured g.f. is correct: the closed form of its coefficients. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = 9 * 10 ^ ((n + 1) / 2 - 1) - 8 * 9 ^ ((n + 1) / 2 - 1) := by
  sorry

end OMA.S_oeis_a050686
