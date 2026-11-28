import Mathlib

/-!
# A335226: Numbers m such that twice the number of unordered Goldbach partitions of 2m is less than the number of unordered Goldbach partitions of 4m.

Source: https://oeis.org/A335226
Credit: @darealpandaboi

Conjecture: the last term in this sequence is a(114) = 22564.

Translation notes.
* G(n) is the number of unordered Goldbach partitions of n into two odd primes: pairs p <= q of
  odd primes with p + q = n (A002375 convention, 4 = 2 + 2 not counted).
* The last term is stated as: 22564 is a term and every term m >= 1 is at most 22564.
* This reproduces the listed terms from 6 on, and for m <= 100000 the last term is 22564 (checked by computer). The data omit m = 2 (G(4) = 0 < G(8) = 1), which would also satisfy the condition; that affects only the index 114, so the index is not stated, only that 22564 is the last term.
-/

namespace OMA.S_oeis_a335226

/-- Unordered partitions of n into two odd primes p <= q. -/
def G (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter
    (fun p => p.Prime ∧ p ≠ 2 ∧ (n - p).Prime ∧ n - p ≠ 2 ∧ p ≤ n - p)).card

theorem main : IsGreatest {m : ℕ | 1 ≤ m ∧ 2 * G (2 * m) < G (4 * m)} 22564 := by
  sorry

end OMA.S_oeis_a335226
