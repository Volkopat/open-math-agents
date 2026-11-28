import Mathlib

/-!
# A140355: Smallest integer such that the first n multiples of a(n) have a number of divisors that is strictly increasing.

Source: https://oeis.org/A140355
Credit: @darealpandaboi

Conjecture: this sequence is finite.

Translation notes.
* a(n) is the least m >= 1 with d(m) < d(2m) < ... < d(nm), where d = number of divisors
  (Nat.divisors (k * m)).card. The sequence is finite exactly when a(n) exists for only finitely
  many n, i.e. the set of n admitting such an m is finite (if n admits m, so does every smaller n).
* This reproduces the listed data a(1..7) = 1, 1, 2, 12, 12, 720, 720 (checked by computer).
-/

namespace OMA.S_oeis_a140355

theorem main :
    {n : ℕ | ∃ m : ℕ, 0 < m ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n →
      (Nat.divisors (i * m)).card < (Nat.divisors (j * m)).card}.Finite := by
  sorry

end OMA.S_oeis_a140355
