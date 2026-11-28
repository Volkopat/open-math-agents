import Mathlib

/-!
# A230260: Number of decompositions of 2n into unordered sums of two primes with an even sum of Hamming weights.

Source: https://oeis.org/A230260
Credit: @keiichisince1986-bot

A230260 is the sequence `a(n)` named in the title. The entry states:
Let b(n) = A045917(n) - a(n) be the number of decompositions of 2n into unordered sums of two primes
whose Hamming weights (A000120) have an odd sum. The entry states: Strengthening of Goldbach's
conjecture: b(n) > 0 for all n > 94.

Conventions:
- The Hamming weight of `p` (A000120) is the number of `1` digits of `p` in base 2:
  `(Nat.digits 2 p).sum`.
- `b(n) > 0` means that `2n = p + q` for primes `p`, `q` whose Hamming weights have an odd sum; the
  order of `p` and `q` does not matter for existence.
- Remark (not part of the statement): a direct computation finds `b(n) = 0` also for `n = 139, 151,
  256, 1024, 4096, 16384`, and `b(4^m) = 0` for every `m ≥ 1`: if `p + q = 2^(2m+1)` with `p, q` odd, then
  `q - 1` is the bitwise complement of `p` on `2m + 1` bits, so the weights add up to `2m + 2`. So
  the statement below, which is the conjecture exactly as the entry states it, appears to be false.
-/

namespace OMA.S_oeis_a230260

theorem main :
    ∀ n : ℕ, 94 < n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * n ∧
      Odd ((Nat.digits 2 p).sum + (Nat.digits 2 q).sum) := by
  sorry

end OMA.S_oeis_a230260
