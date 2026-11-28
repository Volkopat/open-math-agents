import Mathlib

/-!
# A056826: Primes p such that (p^p + 1)/(p + 1) is a prime.

Source: https://oeis.org/A056826
Credit: @divmxnd0x

Conjecture (Thomas Ordowski, Jul 29 2013, stated in A056826): let `b(0) = 1`, `b(1) = 3`,
`b(n+1) = (b(n)^2 + b(n-1)^2)/2`; if `b(n) = p` is prime, then `(p^p + 1)/(p + 1)` is prime.

Formalization notes:
* All `b(n)` are odd, so `b(n)^2 + b(n-1)^2` is even and the division by 2 is exact
  (`b = 1, 3, 5, 17, 157, ...`).
* For an odd prime `p`, `p + 1 ∣ p^p + 1`, so `(p^p + 1)/(p + 1)` is an exact quotient in `ℕ`.
-/

namespace OMA.S_oeis_a056826

/-- Ordowski's sequence: `b 0 = 1`, `b 1 = 3`, `b (n+2) = (b(n+1)^2 + b(n)^2) / 2`. -/
def b : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => (b (n + 1) ^ 2 + b n ^ 2) / 2

/-- Ordowski's conjecture: whenever `b n = p` is prime, `(p^p + 1)/(p + 1)` is prime. -/
theorem main : ∀ n : ℕ, (b n).Prime → (((b n) ^ (b n) + 1) / (b n + 1)).Prime := by
  sorry

end OMA.S_oeis_a056826
