import Mathlib

/-!
# A309291: Primes of the form k!-p where p <= k!/2 is also a prime and k=3,4,5,....

Source: https://oeis.org/A309291
Credit: @xor2k

Formalizes the OEIS A309291 Conjecture 1: every prime number in the interval [k!-k^2, k!-k] for
k>4 has only the form k!-p where p is the n-th prime.

Conventions:
- The conjecture is read as: for every `k > 4` and every prime `q` with
  `k! - k^2 ≤ q ≤ k! - k`, the number `p = k! - q` (the only `p` with `q = k! - p`) is prime.
  The phrase where p is the n-th prime only says that `p` is a prime number.
- `k! - k^2`, `k! - k` and `k! - q` are natural subtraction; for `k > 4` all of them are exact,
  since `k^2 < k!` and `q ≤ k! - k`.
- The entry also remarks that this is easily proved; it is the only conjecture in the entry.
-/

namespace OMA.S_oeis_a309291

/-- For `k > 4`, every prime `q` in `[k! - k^2, k! - k]` has `k! - q` prime. -/
theorem main :
    ∀ k : ℕ, 4 < k → ∀ q : ℕ, q.Prime →
      Nat.factorial k - k ^ 2 ≤ q → q ≤ Nat.factorial k - k → (Nat.factorial k - q).Prime := by
  sorry

end OMA.S_oeis_a309291
