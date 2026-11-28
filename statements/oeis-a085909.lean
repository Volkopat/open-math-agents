import Mathlib

/-!
# A085909: Smallest prime p>prime(n) such that p+prime(n+1)-prime(n) is the next prime after p; or a(n)=0 if no such prime exists.

Source: https://oeis.org/A085909
Credit: @keiichisince1986-bot

A085909 is the sequence `a(n)` named in the title. The entry states:
conjecture: a(n) > 0 for n > 1 (implies the twin prime conjecture). - Reinhard Zumkeller, Jan 26 2004

Conventions:
- We index primes from `0`: `Nat.nth Nat.Prime i` is `prime(i + 1)`. The OEIS index `n > 1` corresponds to
  `i = n - 1 ≥ 1`.
- With `i = n - 1`, `prime(n) = Nat.nth Nat.Prime i`. A prime `p > prime(n)` is `p = Nat.nth Nat.Prime m`
  with `m > i`, and its next prime is `Nat.nth Nat.Prime (m + 1)`. So `a(n) > 0` means that the gap after
  the `i`-th prime occurs again after a later prime. The subtractions of consecutive primes are exact.
-/

namespace OMA.S_oeis_a085909

theorem main :
    ∀ i : ℕ, 1 ≤ i → ∃ m : ℕ, i < m ∧
      Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m = Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i := by
  sorry

end OMA.S_oeis_a085909
