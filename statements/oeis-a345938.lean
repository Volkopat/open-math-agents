import Mathlib

/-!
# A345938: a(n) = uphi(n) / gcd(n-1, uphi(n)), where uphi is unitary totient (or unitary phi) function, A047994.

Source: https://oeis.org/A345938
Credit: @agchua

Comment line of A345938 (entry by Antti Karttunen, Jun 29 2021):
  For all squarefree n (A005117), a(n) = A160595(n), thus if there are any composite solutions to
  the Lehmer's totient conjecture, then they give also a such a subset of positions of 1's in this
  sequence that are not powers of primes. See comments in A160595.
Offset 1. Both parts are stated. A composite solution of Lehmer's totient problem is a composite n
with phi(n) | n-1; the second part says that every such n has a(n) = 1 and is not a prime power.
Definitions: uphi(n) = A047994(n) is the product of p^e - 1 over the prime powers p^e exactly
dividing n (as in the entry's PARI program; uphi(1) = 1); a(n) = uphi(n) / gcd(n-1, uphi(n));
A160595(n) is the numerator of phi(n)/(n-1), with A160595(1) = 1 by convention.
-/

namespace OMA.S_oeis_a345938

/-- A047994: the unitary totient, the product of p^e - 1 over the prime powers p^e exactly dividing n. -/
noncomputable def uphi (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, (p ^ n.factorization p - 1)

/-- A345938: uphi(n) / gcd(n-1, uphi(n)). -/
noncomputable def a (n : ℕ) : ℕ := uphi n / Nat.gcd (n - 1) (uphi n)

/-- A160595: the numerator of phi(n)/(n-1), and 1 for n = 1. -/
noncomputable def A160595 (n : ℕ) : ℤ :=
  if n = 1 then 1 else ((Nat.totient n : ℚ) / ((n : ℚ) - 1)).num

/-- a(n) = A160595(n) for squarefree n; a composite n with phi(n) | n-1 has a(n) = 1 and is not a
prime power. -/
theorem main : (∀ n : ℕ, 1 ≤ n → Squarefree n → (a n : ℤ) = A160595 n) ∧
    (∀ n : ℕ, 1 < n → ¬ n.Prime → Nat.totient n ∣ n - 1 → a n = 1 ∧ ¬ IsPrimePow n) := by
  sorry

end OMA.S_oeis_a345938
