import Mathlib

/-!
# A200652: a(n) = least k with -3<k<2*n such that n*(n+1)+k and n*(n+1)+k+2 are twin primes, or 0 if no such k exists.

Source: https://oeis.org/A200652
Credit: @darealpandaboi

Conjecture: no more 0 values if n > 433 (only 11 values are zero for n < 434).

Translation notes.
* k = 0 never works (n(n+1) is even and at least 2, and n(n+1) = 2 gives 2, 4), so a(n) = 0
  means exactly that no k with -3 < k < 2n works.
* Writing m = n(n+1) + k, the condition -3 < k < 2n reads n(n+1) <= m + 2 and m < n(n+1) + 2n,
  which keeps everything in ℕ.
* This reproduces the listed data (checked by computer); for n <= 433 there are exactly 11 zeros,
  the last at n = 433, and none for 433 < n < 3000.
-/

namespace OMA.S_oeis_a200652

theorem main : ∀ n : ℕ, 433 < n →
    ∃ m : ℕ, n * (n + 1) ≤ m + 2 ∧ m < n * (n + 1) + 2 * n ∧ m.Prime ∧ (m + 2).Prime := by
  sorry

end OMA.S_oeis_a200652
