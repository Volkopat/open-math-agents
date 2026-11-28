import Mathlib

/-!
# A246776: a(n) = floor(prime(n)^(1+1/n)) - prime(n+1).

Source: https://oeis.org/A246776
Credit: @agchua

Comment line of A246776 (double quotation marks replaced by single ones here):
  The Firoozbakht Conjecture, 'prime(n)^(1/n) is a strictly decreasing function of n' is true
  if and only if a(n) is nonnegative for all n, n>1.
Offset 1. prime(n) is the n-th prime (A000040): prime(1) = 2, prime(2) = 3, ...; here
prime(n) = Nat.nth Nat.Prime (n - 1). Powers with real exponents are Real.rpow, and floor is
Int.floor (data 1, 0, 1, 0, 4, 2, 6, ...). The Firoozbakht conjecture is stated as: the function
n |-> prime(n)^(1/n) is strictly decreasing on n >= 1. The claim is the equivalence of the two
statements; it does not assert either of them.
-/

namespace OMA.S_oeis_a246776

/-- prime(n), the n-th prime (A000040, offset 1). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- a(n) = floor(prime(n)^(1+1/n)) - prime(n+1). -/
noncomputable def a (n : ℕ) : ℤ :=
  ⌊(prime n : ℝ) ^ (1 + 1 / (n : ℝ))⌋ - (prime (n + 1) : ℤ)

/-- The Firoozbakht conjecture (prime(n)^(1/n) strictly decreasing for n >= 1) holds if and only
if a(n) >= 0 for every n > 1. -/
theorem main :
    StrictAntiOn (fun n : ℕ => (prime n : ℝ) ^ (1 / (n : ℝ))) (Set.Ici 1) ↔
      ∀ n : ℕ, 1 < n → 0 ≤ a n := by
  sorry

end OMA.S_oeis_a246776
