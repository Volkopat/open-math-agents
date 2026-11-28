import Mathlib

/-!
# A137997: Numbers which are not the sum of a triangular number and zero or a prime = 3 (mod 4).

Source: https://oeis.org/A137997
Credit: @darealpandaboi

Conjecture (Zhi-Wei Sun): n = 216 is the only number not of the form n = p + k(k+1)/2 with p a
prime or zero, and more precisely the numbers A137997(1..112) = 2, ..., 90441 are the only
numbers which cannot be written in this form with p = 0 or p = 3 (mod 4).

Translation notes.
* Triangular numbers are k(k+1)/2 for k >= 0 (so 0 is triangular); numbers are positive.
* Part 1: every positive n other than 216 is p + k(k+1)/2 with p = 0 or p prime.
* Part 2: the listed 112 terms are all terms; since the largest is 90441, this is stated as:
  every n > 90441 is p + k(k+1)/2 with p = 0 or (p prime and p = 3 mod 4). The terms up to
  90441 are a finite computation that reproduces the listed data (112 terms, last 90441,
  checked by computer), so nothing beyond them needs to be asserted.
* Checked by computer: for 1 <= n <= 100000, 216 is the only exception to part 1.
-/

namespace OMA.S_oeis_a137997

theorem main :
    (∀ n : ℕ, 0 < n → n ≠ 216 → ∃ p k : ℕ, (p = 0 ∨ p.Prime) ∧ n = p + k * (k + 1) / 2) ∧
    (∀ n : ℕ, 90441 < n →
      ∃ p k : ℕ, (p = 0 ∨ (p.Prime ∧ p % 4 = 3)) ∧ n = p + k * (k + 1) / 2) := by
  sorry

end OMA.S_oeis_a137997
