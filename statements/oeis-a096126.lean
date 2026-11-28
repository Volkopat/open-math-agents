import Mathlib

/-!
# A096126: a(n) is the least integer of the form (n^2)!/(n!)^k.

Source: https://oeis.org/A096126
Credit: @agchua

Comment of A096126 (unsigned; the entry is by Amarnath Murthy, Jul 03 2004, edited by Don Reble):
  (n^2)!/(n!)^(n+1) is an integer for every n (see A057599). Hence k >= n+1. Conjecture: k=n+1 only when n is prime or a power of a prime.
The sequence has offset 1. The least integer of the form (n^2)!/(n!)^k is reached at the largest k
with (n!)^k dividing (n^2)!, so the k of the comment is the greatest element of exps n below. The
claim is stated for n ≥ 2: for n = 1 every k works (1!^k = 1), so there is no largest k.
IsPrimePow n (n = p^j with p prime and j ≥ 1) covers both the primes and the powers of primes.
-/

namespace OMA.S_oeis_a096126

/-- The exponents k for which (n!)^k divides (n^2)!. -/
def exps (n : ℕ) : Set ℕ := {k : ℕ | Nat.factorial n ^ k ∣ Nat.factorial (n ^ 2)}

/-- The comment's conjecture, for n ≥ 2: if the largest such k is n + 1, then n is a prime or a
power of a prime. -/
theorem main : ∀ n : ℕ, 2 ≤ n → IsGreatest (exps n) (n + 1) → IsPrimePow n := by
  sorry

end OMA.S_oeis_a096126
