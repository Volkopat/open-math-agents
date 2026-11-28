import Mathlib

/-!
# A335250: Numbers m such that twice the number of unordered Goldbach partitions of 2m equals the number of unordered Goldbach partitions of 4m.

Source: https://oeis.org/A335250
Credit: @darealpandaboi

Conjecture: the last term in this sequence is a(45) = 11749.

Translation notes.
* G(n) is the number of unordered Goldbach partitions of n into two odd primes: pairs p <= q of
  odd primes with p + q = n (A002375 convention, 4 = 2 + 2 not counted).
* The last term is stated as: 11749 is a term and every term m >= 1 is at most 11749.
* This reproduces all 45 listed terms 1, 4, 9, ..., 6946, 11749 and finds no other term m <= 100000 (checked by computer). The index 45 is then implied.
-/

namespace OMA.S_oeis_a335250

/-- Unordered partitions of n into two odd primes p <= q. -/
def G (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter
    (fun p => p.Prime ∧ p ≠ 2 ∧ (n - p).Prime ∧ n - p ≠ 2 ∧ p ≤ n - p)).card

theorem main : IsGreatest {m : ℕ | 1 ≤ m ∧ 2 * G (2 * m) = G (4 * m)} 11749 := by
  sorry

end OMA.S_oeis_a335250
