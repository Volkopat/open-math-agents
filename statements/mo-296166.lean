import Mathlib

/-!
# Does n and (n-1)/2 being strong probable primes imply n prime?

Source: https://mathoverflow.net/questions/296166 (CC BY-SA 3.0).

A strong probable prime (to base `2`) is a positive integer `m` which is either `2`, or such that,
writing `m - 1 = d · 2^s` with `d` odd, `2^d ≡ 1 (mod m)` or `2^(d · 2^r) ≡ -1 (mod m)` for some
`0 ≤ r < s`. All primes are strong probable primes; the composite ones are the strong
pseudoprimes (OEIS A001262). Question: if both `n` and `(n-1)/2` are strong probable primes, does
it follow that `n` is prime? `main` states the expected yes (checked for `n < 2^65`).

The post writes `m = d · 2^s`; the standard definition it cites (A001262, "all primes are strong
probable primes", and its reduction for `n = 2m + 1` to `2^m ≡ ±1 (mod n)`) is `m - 1 = d · 2^s`,
which is used here. `n` is odd, so that `(n-1)/2` is an integer.
-/

namespace OMA.S_mo_296166

/-- `m` is a strong probable prime to base `2`. -/
def StrongProbablePrime (m : ℕ) : Prop :=
  m = 2 ∨ (0 < m ∧ ∃ d s : ℕ, Odd d ∧ m - 1 = d * 2 ^ s ∧
    (2 ^ d ≡ 1 [MOD m] ∨ ∃ r < s, (2 : ℤ) ^ (d * 2 ^ r) ≡ -1 [ZMOD m]))

theorem main : ∀ n : ℕ, Odd n → StrongProbablePrime n → StrongProbablePrime ((n - 1) / 2) →
    n.Prime := by
  sorry

end OMA.S_mo_296166
