import Mathlib

/-!
# A061265: Number of squares between n-th prime and (n+1)st prime.

Source: https://oeis.org/A061265
Credit: @agchua

Comment of A061265 by Vladeta Jovovic, May 01 2003:
  Legendre's conjecture (still open) that there is always a prime between n^2 and (n+1)^2 is
  equivalent to conjecturing that a(n) <= 1 for all n.
Offset 1. prime(n) is the n-th prime (A000040): prime(1) = 2, prime(2) = 3, ...; here
prime(n) = Nat.nth Nat.Prime (n - 1). a(n) counts the squares k^2 with prime(n) < k^2 < prime(n+1)
(data 0, 1, 0, 1, 0, 1, 0, 0, 1, ...). Legendre's conjecture is stated for every m >= 1 (there is
no prime between 0^2 and 1^2), and a(n) <= 1 is required for every n >= 1, the offset.
The claim is the equivalence of the two statements; it does not assert either of them.
-/

namespace OMA.S_oeis_a061265

/-- prime(n), the n-th prime (A000040, offset 1). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- a(n) = A061265(n): the number of squares k^2 with prime(n) < k^2 < prime(n+1). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range (prime (n + 1))).filter
    (fun k => prime n < k ^ 2 ∧ k ^ 2 < prime (n + 1))).card

/-- Legendre's conjecture (a prime between m^2 and (m+1)^2 for every m >= 1) holds if and only
if a(n) <= 1 for every n >= 1. -/
theorem main :
    (∀ m : ℕ, 1 ≤ m → ∃ p : ℕ, p.Prime ∧ m ^ 2 < p ∧ p < (m + 1) ^ 2) ↔
      ∀ n : ℕ, 1 ≤ n → a n ≤ 1 := by
  sorry

end OMA.S_oeis_a061265
