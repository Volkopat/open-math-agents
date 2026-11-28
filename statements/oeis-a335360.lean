import Mathlib

/-!
# A335360: Numbers m such that the number of unordered Goldbach partitions of 2m is greater than the number of unordered Goldbach partitions of 4m.

Source: https://oeis.org/A335360
Credit: @darealpandaboi

Conjecture: a(5) = 353 is the last term in this sequence.

Translation notes.
* G(n) is the number of unordered Goldbach partitions of n into two odd primes: pairs p <= q of
  odd primes with p + q = n (A002375 convention, 4 = 2 + 2 not counted).
* The last term is stated as: 353 is a term and every term m >= 1 is at most 353.
* This reproduces the listed data 17, 32, 38, 143, 353 and finds no other term m <= 100000 (checked by computer).
-/

namespace OMA.S_oeis_a335360

/-- Unordered partitions of n into two odd primes p <= q. -/
def G (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter
    (fun p => p.Prime ∧ p ≠ 2 ∧ (n - p).Prime ∧ n - p ≠ 2 ∧ p ≤ n - p)).card

theorem main : IsGreatest {m : ℕ | 1 ≤ m ∧ G (4 * m) < G (2 * m)} 353 := by
  sorry

end OMA.S_oeis_a335360
